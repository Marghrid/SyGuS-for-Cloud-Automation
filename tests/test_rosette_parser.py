import unittest

from synthesizer.encoder.json_to_rosette import Json2RosetteEncoder


class RosetteParserTests(unittest.TestCase):

    def test1(self):
        encoder = Json2RosetteEncoder()
        self.assertEqual(encoder.parse_rosette_output("(define (f?_11 x) (child (index x 0) \"Item\"))"),
                         ('child', (('index', ('x', 0)), "Item")))

    def test2(self):
        encoder = Json2RosetteEncoder()
        out = encoder.parse_rosette_output("(define (f?_2 x) (descendant (index x 0) \"Item\"))")
        self.assertEqual(out, ('descendant', (('index', ('x', 0)), "Item")))

    def test3(self):
        encoder = Json2RosetteEncoder()
        out = encoder.convert_rosette_to_jsonpath("(define (f?_11 x) (child (index x 0) \"Item\"))")
        self.assertEqual(out, '$[0].Item')

    def test4(self):
        encoder = Json2RosetteEncoder()
        out = encoder.convert_rosette_to_jsonpath(
            '(define (f$_4 x) (syntEq (index (descendant (index x 1) "Name") 0) "stopping"))')
        self.assertEqual(out, '($[1]..Name[0] == "stopping")')
