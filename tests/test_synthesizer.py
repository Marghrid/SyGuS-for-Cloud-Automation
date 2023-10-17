import sys
import unittest

from synthesizer.data_transforms_synthesizer import synthesize_data_transforms


class RosetteParserTests(unittest.TestCase):

    def test1(self):
        example = {"name": "f0",
                   "constraints": [
                       {"inputs": ['a', 'b', 'c'], "output": "c"},
                       {"inputs": ['e', 'f', 'd'], "output": "d"},
                       {"inputs": ['v', 'x', 'f'], "output": "f"},
                       {"inputs": ['hello', ':)', 'n'], "output": 'n'},
                   ]}
        result = synthesize_data_transforms(sys._getframe().f_code.co_name, [example], 60, False)
        self.assertEqual(result[0]['solution'], '$[2]')

    def test2(self):
        example = {"name": "f0",
                   "constraints": [
                       {"inputs": [{'a': 4, 'b': 5, 'c': 6}], "output": 4},
                       {"inputs": [{'e': 5, 'a': 5, 'd': 6}], "output": 5},
                       {"inputs": [{'v': 4, 'x': 3, 'a': 7}], "output": 7},
                   ]}
        result = synthesize_data_transforms(sys._getframe().f_code.co_name, [example], 60, False)
        self.assertEqual(result[0]['solution'], '$[0].a')

    def test3(self):
        example = {"name": "f0",
                   "constraints": [
                       {"inputs": [{'a': 4, 'b': 5, 'c': 6}], "output": 4},
                       {"inputs": [{'e': 5, 'a': 5, 'd': 6}], "output": 4},
                       {"inputs": [{'v': 4, 'x': 3, 'a': 7}], "output": 7},
                   ]}
        result = synthesize_data_transforms(sys._getframe().f_code.co_name, [example], 60, False)
        self.assertEqual(result[0]['solution'], '(unsat)')

    def test4(self):
        example = {"name": "f0",
                   "constraints": [
                       {"inputs": [{'lvl0': {'a': 4, 'b': 5, 'c': 6}}], "output": 4},
                       {"inputs": [{'e': 5, 'a': 5, 'd': 6}], "output": 5},
                       {"inputs": [{'v': 4, 'x': 3, 'a': 7}], "output": 7},
                   ]}
        result = synthesize_data_transforms(sys._getframe().f_code.co_name, [example], 60, False)
        self.assertEqual(result[0]['solution'], '$[0]..a[0]')
