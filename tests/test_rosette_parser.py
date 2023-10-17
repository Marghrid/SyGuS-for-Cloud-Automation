import unittest

from synthesizer.to_rosette import convert_rosette_to_jsonpath, parse_rosette_output


class RosetteParserTests(unittest.TestCase):

    def test1(self):
        self.assertEqual(parse_rosette_output("(define (f?_11 x) (child (index x 0) \"Item\"))"),
                         ('child', (('index', ('x', 0)), "Item")))

    def test2(self):
        self.assertEqual(parse_rosette_output("(define (f?_2 x) (descendant (index x 0) \"Item\"))"),
                         ('descendant', (('index', ('x', 0)), "Item")))

    def test3(self):
        self.assertEqual(convert_rosette_to_jsonpath("(define (f?_11 x) (child (index x 0) \"Item\"))"), '$[0].Item')

    def test4(self):
        self.assertEqual(
            convert_rosette_to_jsonpath('(define (f$_4 x) (syntEq (index (descendant (index x 1) "Name") 0) "stopping"))'),
            '$[1]..Name[0] == "stopping"')
