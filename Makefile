POLYC = polyc

all: minicaml2

minicaml2: minicaml2.sml
	$(POLYC) -o $@ $<

demo: minicaml2
	./minicaml2 demo.mml

repl: minicaml2
	./minicaml2

samples: minicaml2
	@for f in samples/*.mml; do \
	  echo "========== $$f =========="; \
	  ./minicaml2 $$f; \
	done

clean:
	rm -f minicaml2

.PHONY: all demo repl samples clean
