(TeX-add-style-hook
 "test"
 (lambda ()
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art10"
    "listings"
    "color")
   (TeX-add-symbols
    "lstlanguagefiles"))
 :latex)

