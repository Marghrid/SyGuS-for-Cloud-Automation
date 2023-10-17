import unittest

from synthesizer.to_rosette import parse_rosette_output


class RosetteParserTests(unittest.TestCase):

    def test1(self):
        self.assertEqual(parse_rosette_output("(define (f?_11 x) (child (index x 0) \"Item\"))"),
                         ('child', (('index', ('x', 0)), "Item")))

    def test2(self):
        self.assertEqual(parse_rosette_output("(define (f?_2 x) (descendant (index x 0) \"Item\"))"),
                         ('descendant', (('index', ('x', 0)), "Item")))
