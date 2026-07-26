POLYC = polyc

all: minicaml2

minicaml2: minicaml2.sml
	$(POLYC) -o $@ $<

demo: minicaml2
	./minicaml2 demo.mml

repl: minicaml2
	./minicaml2

clean:
	rm -f minicaml2

.PHONY: all demo repl clean
