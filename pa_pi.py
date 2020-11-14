from collections import OrderedDict
from enum import Enum
import re
import sys
import operator



from bs4 import BeautifulSoup
from pprint import pprint

import pandas as pd

from selenium.webdriver import Chrome
from selenium.common.exceptions import TimeoutException
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.common.by import By 
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.support.ui import WebDriverWait
from tabulate import tabulate
from time import sleep, ctime
 
_FACTIONS = [
    'ambas', 'baltaks', 'bescods', 'firaks', 'geodens', 'gleens', 'hadsch-hallas',
    'itars', 'ivits', 'lantids', 'nevlas', 'taklons', 'terrans', 'xenos']

_TECH_TRACKS = ['terra', 'nav', 'int', 'gaia', 'eco', 'sci']

_ACTIONS = ['pass', 'build', 'up', 'charge', 'spend', 'action', 'special']

glist = []

class Res(Enum):
    COIN = 1
    ORE = 2
    KNOWLEDGE = 3
    QIC = 4
    POWER = 5
    PT = 6
    VP = 7


class ChangeType(Enum):
    GAIN = 1
    LOSS = 2


class StateChange:
    """Represents a single change in the game state."""

    _RESOURCE_MAP = {
        'c': Res.COIN,
        'o': Res.ORE,
        'k': Res.KNOWLEDGE,
        'q': Res.QIC,
        'pw': Res.POWER,
        't': Res.PT,
        'vp': Res.VP,
    }

    def __init__(self, state_change_string):
        if not state_change_string:
            raise ValueError('state_change_string cannot be empty.')

        # Determine whether this state change marks the loss or gain of resources.
        if state_change_string[0] == '-':
            self.type = ChangeType.LOSS
        else:
            self.type = ChangeType.GAIN

        # Determine which resource the state change refers to.
        for res_string, res_type in StateChange._RESOURCE_MAP.items():
            if state_change_string.endswith(res_string):
                self.resource = res_type
                break

                # Determine the quantity of resource gained or lost.
        try:
            self.quantity = int(re.findall(r'\d+', state_change_string)[0])
        except IndexError:
            print('No quantity found in ' + state_change_string)
            sys.exit(1)

    def __repr__(self):
        return 'StateChange(type={}, resource={}, quantity={})'.format(
            self.type, self.resource, self.quantity)


class LogItem:
    """A single log item."""

    def __init__(self, text, faction, events):
        """
        Constructs a log item.

        :param text: Text describing what was logged.
        :param faction: The faction (if any) whose action created the log item.
        :param events: A list of state-modifying events that occurred during the primary action.
        """
        self.text = text
        self.faction = faction
        self.events = events

    def __repr__(self):
        return "LogItem(text='{}', faction={}, events={})".format(
            self.text, self.faction, self.events)

    @staticmethod
    def _get_faction(text):
        """Check whether an action had an associated faction."""
        for faction in _FACTIONS:
            if faction in text:
                return faction
        return None

    @staticmethod
    def _compute_events(actions_html, state_change_html):
        """Compute the events that occurred during each action."""
        actions = [act.string for act in actions_html.find_all('div')]
        state_changes = [st.string for st in state_change_html.find_all('div')]
        events = []
        for action, state_change in zip(actions, state_changes):
            action = action.strip()
            state_change_list = state_change.strip().replace(',', '').split(' ')
            change_list = []
            for change in state_change_list:
                if change.strip():
                    change_list.append(StateChange(change.strip()))
                else:
                    change_list.append(None)
            events.append((action, change_list))
        return events

    @staticmethod
    def parse_from_html(row):
        """Constructs a LogItem from a <tr> HTML element."""
        cols = row.find_all('td')
        if len(cols) < 1:
            raise ValueError('The row {} is empty.'.format(row))
        # We check for a faction regardless of the number of columns in the row.
        text = cols[0].string.strip()
        faction = LogItem._get_faction(text)
        events = None
        if len(cols) == 3:
            # There are three columns in the row, so this action did have an effect on the game state.
            events = LogItem._compute_events(cols[1], cols[2])
        return LogItem(text, faction, events)


class GameLog:
    """A log of all actions taken in a game."""

    def __init__(self, factions, items):
        """Constructs a game log object."""
        self.factions = factions
        self.items = items

    @staticmethod
    def parse_from_html(html):
        """Parses a game log from an HTML element."""
        log_rows = html.find_all('tr', html.table.tbody)
        # Reverse the rows in the log so that the actions are in the correct sequence.
        log_rows.reverse()
        items = [LogItem.parse_from_html(row) for row in log_rows]
        factions = set()
        for item in items:
            if item.faction:
                stripped_faction = item.faction.strip()
                if stripped_faction not in factions:
                    factions.add(stripped_faction)
        return GameLog(factions, items)


class WinStats:
    """Object which tracks all stats related to VP counts."""

    def __init__(self):
        self.matches = 0
        self.wins = 0
        self.losses = 0

    def update_wins(self, win):
        self.matches += 1
        if win:
            self.wins += 1
        else:
            self.losses += 1

    @staticmethod
    def get_winner(log):
        faction_stats = {faction: 10 for faction in log.factions}
        for item in log.items:
            if item.faction and item.events:
                for event in item.events:
                    action = event[0]
                    changes = event[1]
                    for change in changes:
                        if change.resource == Res.VP:
                            assert change.type is ChangeType.GAIN or change.type is ChangeType.LOSS
                            # If this doesn't change VP count, ignore it.
                            if not change.resource == Res.VP or action == 'bid':
                                continue
                            if change.type is ChangeType.GAIN:
                                faction_stats[item.faction] += change.quantity
                            else:
                                faction_stats[item.faction] -= change.quantity
        print(faction_stats)
        if faction_stats:
            return max(faction_stats, key=faction_stats.get)
        else:
            return None


class VPStats:
    """Object which tracks all stats related to VP counts."""

    def __init__(self):
        self.vp = 10
        self.vp_lost_from_leech = 0
        self.vp_from_round_scoring = 0
        self.vp_from_boosters = 0
        self.vp_from_endgame = 0
        self.vp_from_techs = 0
        self.vp_from_adv_techs = 0
        self.vp_from_feds = 0
        self.vp_from_qic_act = 0
        self.vp_from_tracks = 0
        self.vp_from_resources = 0

    def update_vp(self, action, change):
        """Increment VP statistics according to the action performed."""
        # change.type must be either ChangeType.GAIN or ChangeType.LOSS
        assert change.type is ChangeType.GAIN or change.type is ChangeType.LOSS
        # If this doesn't change VP count, ignore it.
        if not change.resource == Res.VP:
            return
        elif 'round' in action:
            self.vp_from_round_scoring += change.quantity
        elif 'booster' in action:
            self.vp_from_boosters += change.quantity
        elif 'final' in action:
            self.vp_from_endgame += change.quantity
        elif 'tech' in action:
            self.vp_from_techs += change.quantity
        elif 'adv' in action:
            self.vp_from_adv_techs += change.quantity
        elif 'federation' == action:
            self.vp_from_feds += change.quantity
        elif 'qic' in action:
            self.vp_from_qic_act += change.quantity
        elif action in _TECH_TRACKS:
            self.vp_from_tracks += change.quantity
        elif 'spend' == action:
            self.vp_from_resources += change.quantity
        elif 'charge' == action:
            self.vp_lost_from_leech -= change.quantity
        # Increment or decrement total VP stats accordingly.
        if change.type is ChangeType.GAIN:
            self.vp += change.quantity
        elif change.type is ChangeType.LOSS:
            self.vp -= change.quantity


class ResourceStats:
    """Object which tracks all stats related to non-VP resources."""

    _RESOURCE_TO_FIELD_MAP = {
        Res.POWER: 'power',
        Res.COIN: 'coins',
        Res.ORE: 'ore',
        Res.KNOWLEDGE: 'knowledge',
        Res.QIC: 'qic',
        Res.PT: 'pt',
    }

    def __init__(self):
        self.leech = 0
        self.power = 0
        self.coins = 0
        self.ore = 0
        self.knowledge = 0
        self.qic = 0
        self.pt = 0

    def update_resources(self, action, change):
        """Increment resource statistics according to action performed."""
        # Currently we only track total number of resources gained.
        if change.type is ChangeType.LOSS:
            return
        # The type of change should be ChangeType.GAIN if it is not ChangeType.LOSS.
        assert change.type == ChangeType.GAIN
        # Handle leech specially as it depends on the action taken, not the resource.
        if 'charge' == action:
            self.leech += change.quantity

        field = ResourceStats._RESOURCE_TO_FIELD_MAP[change.resource]
        current_value = getattr(self, field)
        setattr(self, field, current_value + change.quantity)


class FactionStats(VPStats, ResourceStats, WinStats):
    """Track statistics for a specific faction in a game."""

    def __init__(self, faction):
        self.faction = faction
        VPStats.__init__(self)
        ResourceStats.__init__(self)
        WinStats.__init__(self)

    def augment(self, event):
        """Augment faction stats with data from a new event."""
        action = event[0]
        changes = event[1]
        for change in changes:
            if change.resource == Res.VP:
                self.update_vp(action, change)
            else:
                self.update_resources(action, change)


class Stats:
    """Compute statistics from a given GameLog."""

    def __init__(self):
        pass
        self.log = None
        self.faction_stats = {}

    def update(self, log):
        self.log = log
        faction_stats = {faction: FactionStats(faction) for faction in self.log.factions}
        winner = WinStats.get_winner(self.log)
        print(winner)

        for item in self.log.items:
            if item.faction and item.events:
                for event in item.events:
                    if item.faction not in self.faction_stats:
                        self.faction_stats[item.faction] = FactionStats(item.faction)
                    self.faction_stats[item.faction].augment(event)

        if winner:
            for f in self.log.factions:
                if f == winner:
                    self.faction_stats[f].update_wins(True)
                else:
                    self.faction_stats[f].update_wins(False)

        # if winner:
        #     [self.faction_stats[f].update_wins(f == winner) for f in self.log.factions]
        # for faction in self.log.factions:
        #     self.faction_stats[faction].update_wins(faction == winner)


    def breakdown_vp(self):
        """Perform a breakdown of the VP gained by each faction."""
        # First print a breakdown of the number of points gained from each category.
        print('VP breakdown:')
        headers = ['Faction', 'Total VP', 'Round', 'Boosters', 'Endgame', 'Techs', 'Adv. Techs', 'Feds', 'QIC Actions',
                   'Tracks', 'Resources', 'Leech']
        rows = []
        for faction, stats in self.faction_stats.items():
            rows.append([
                faction,
                stats.vp,
                stats.vp_from_round_scoring,
                stats.vp_from_boosters,
                stats.vp_from_endgame,
                stats.vp_from_techs,
                stats.vp_from_adv_techs,
                stats.vp_from_feds,
                stats.vp_from_qic_act,
                stats.vp_from_tracks,
                stats.vp_from_resources,
                stats.vp_lost_from_leech,
            ])
        print(tabulate(rows, headers=headers))
        print()
        # Next, print a breakdown of what percentage of the total VP each category contributed.
        print('VP Percentages:')
        headers.remove('Total VP')
        rows = []
        for faction, stats in self.faction_stats.items():
            rows.append([
                faction,
                stats.vp_from_round_scoring / stats.vp * 100,
                stats.vp_from_boosters / stats.vp * 100,
                stats.vp_from_endgame / stats.vp * 100,
                stats.vp_from_techs / stats.vp * 100,
                stats.vp_from_adv_techs / stats.vp * 100,
                stats.vp_from_feds / stats.vp * 100,
                stats.vp_from_qic_act / stats.vp * 100,
                stats.vp_from_tracks / stats.vp * 100,
                stats.vp_from_resources / stats.vp * 100,
                stats.vp_lost_from_leech / stats.vp * 100,
            ])
        print(tabulate(rows, headers=headers, floatfmt='.2f'))
        print()

    def breakdown_resources(self):
        """Performs a breakdown of the resources gained by each faction."""
        print('Resources breakdown:')
        headers = ['Faction', 'Power', 'Leech', 'Coins', 'Ore', 'Knowledge', 'QIC', 'Power Tokens']
        rows = []
        for faction, stats in self.faction_stats.items():
            rows.append([
                faction,
                stats.power,
                stats.leech,
                stats.coins,
                stats.ore,
                stats.knowledge,
                stats.qic,
                stats.pt,
            ])
        print(tabulate(rows, headers=headers))
        print()

    def breakdown_wins(self):
        """Performs a breakdown of the wins gained by each faction."""
        print('Win breakdown:')
        headers = ['Faction', 'Matches', 'Wins', 'Losses', 'Win %']
        rows = []
        for faction, stats in self.faction_stats.items():
            winpct = 0
            if stats.wins > 0:
                winpct = (stats.wins / (stats.wins + stats.losses)) * 100
            rows.append([
                faction,
                stats.wins + stats.losses,
                stats.wins,
                stats.losses,
                winpct,
            ])
        print(tabulate(rows, headers=headers, floatfmt='.2f'))
        print()

    def breakdown(self):
        """Breakdown VP and resources."""
        self.breakdown_vp()
        self.breakdown_resources()
        self.breakdown_wins()


# def test_main():
#     """Use a local HTML file to test stats breakdown."""
#     html = None
#     with open('tester_full.html') as f:
#         html = f.read()
#
#     if html:
#         soup = BeautifulSoup(html, 'lxml')
#         raw_game_log = soup.find('div', class_='col-12 order-last mt-4')
#         log = GameLog.parse_from_HTML(raw_game_log)
#         stats = Stats()
#         stats.update(log)
#         stats.breakdown()

def stats_test(browser):
    gamelist = [
        'https://www.boardgamers.space/game/Swift-picture-1150',
         'https://www.boardgamers.space/game/Telling-station-7416',
         'https://www.boardgamers.space/game/Blunt-character-8326',
        'https://www.boardgamers.space/game/10mgame',
         'https://www.boardgamers.space/game/Flashing-doubt-9666',
         'https://www.boardgamers.space/game/Daniel-1day-nobidding-23',
         'https://www.boardgamers.space/game/12345',
         'https://www.boardgamers.space/game/Daniel-1day-nobidding-15',
         'https://www.boardgamers.space/game/Daniel-1day-nobidding-17'
    ]

    stats = Stats()
    for game in gamelist:
       parse_game(browser, game, stats)
    print(glist)


def parse_game(browser, url, stats):
    browser.get(url)
    delay = 10
    try:
        WebDriverWait(browser, delay).until(
            EC.presence_of_element_located((By.ID, 'game-iframe'))
        )
        browser.switch_to.frame('game-iframe')
    except TimeoutException:
        print('Loading took too much time!')
    else:
        html = browser.page_source

    if html:

        soup = BeautifulSoup(html, 'lxml')

        # html = None
        # with open('tester_full.html') as f:
        #     html = f.read()

        soup = BeautifulSoup(html, 'lxml')

        raw_game_log = soup.find('div', class_='col-12 order-last mt-4')

        if soup.body.findAll(text='Game Ended'):
            log = GameLog.parse_from_html(raw_game_log)
            stats.update(log)
            stats.breakdown()
            glist.append(url)
        else:
            print('Game not finished!')


def main():
    opts = Options()
    opts.headless = True
    assert opts.headless  # Operating in headless mode
    browser = Chrome(options=opts)

    stats = Stats()
    if len(sys.argv) > 1:
        if sys.argv[1].upper() == 'TEST':
            stats_test(browser)
        else:
            parse_game(browser, sys.argv[1], stats)
    else:

        gamelist = []

        browser.get('https://www.boardgamers.space')
        sleep(5)
        results = browser.find_elements_by_class_name('btn')
        results[4].click()
        # for p in results:
        #     if p.text == 'All games':
        #         print(p.text)
        #         p.click()
        #         continue

        sleep(3)
        finished = False
        while not finished:
            results = browser.find_elements_by_class_name('game-name')
            for r in results:
                game_name = r.text
                if len(game_name):
                    if game_name not in gamelist:
                        gamelist.append(game_name)
        #
            results = browser.find_elements_by_class_name('page-link')
            links = []
            for r in results:
                t = r.text
                if t == '›':
                    links.append(r)

            if len(links) > 1:
                links[1].click()
            else:
                print('no link')
                finished = True
            sleep(2)

            if len(gamelist) > 5000:
                finished = True
            else:
                print(len(gamelist))

        for g in gamelist:
            game = 'https://www.boardgamers.space/game/' + g
            parse_game(browser, game, stats)

        # for g in gamelist:
        #     game = 'https://www.boardgamers.space/game/' + g
        #     print(game)
        # print(len(gamelist))

    browser.close()
    exit(0)


if __name__=='__main__':
    main()