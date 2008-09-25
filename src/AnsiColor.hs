module AnsiColor where

import Data.Char

esc x = [chr 27] ++ "[" ++ x

normal = esc "0m"

black = esc "30m"
red = esc "31m"
green = esc "32m"
yellow = esc "33m"
blue = esc "34m"
magenta = esc "35m"
cyan = esc "36m"
white = esc "37m"

reset = esc "0;0m"
bold = esc "1m"
dim = esc "2m"
underscore = esc "4m"
blink = esc "5m"
reverse = esc "7m"
hidden = esc "8m"

blackBg = esc "40m"
redBg = esc "41m"
greenBg = esc "42m"
yellowBg = esc "43m"
blueBg = esc "44m"
magentaBg = esc "45m"
cyanBg = esc "46m"
whiteBg = esc "47m"

clrScr = esc "2J" ++ esc "H"
