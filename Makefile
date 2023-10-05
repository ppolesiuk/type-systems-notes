NAME = type-systems
.PHONY: $(NAME).pdf clean clean-all

$(NAME).pdf: $(NAME).tex
		latexmk -pdf -use-make $<

clean:
		latexmk -c

clean-all:
		latexmk -C
