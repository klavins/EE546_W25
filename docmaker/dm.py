import sys
import re

# Converts to lean to markdown by converting comment blocks to markdown and code to markdown code blocks. 
# The resulting markdown file can be viewed with your favorite viewer, or convered to html with something 
# like pandoc -o build/output.html build/input.md --toc --standalone --mathjax --markdown-headings=atx

f = open(sys.argv[1], "r")

data = f.read()

## print(data)

comment = r'(?s:(/-.*?-/))'

for str in re.split(comment, data)[1:]:
    if len(str) > 1 and str[0] == '/' and str[1] == '-':
        markdown = str[2:len(str)-2]
        print(markdown)
    else:
        code = str.lstrip().rstrip()
        if len(code) > 0:
            print("```hs")   # there is no lean highlighter with my chrome plugin
            print(code)
            print('```')
