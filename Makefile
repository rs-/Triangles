COQDOCFLAGS?=-interpolate -utf8 -g -s -l --with-header coq-header.html --with-footer coq-footer.html
-include Makefile.coq

Makefile.coq:
	coq_makefile -f Make -o $@

doc: rmhtml html/toc.html html/coqdoc.css html/Symbola.woff
	sed -i '' -e 's/type="/data-type="/g;s/data-data/data/g;s/:=/≔/g;s/type="notation">◯/type="notation">τ/g' html/*.html html/*.css
	perl -i -p -0 -e 's/(\n<br\/>\n)+/<br\/>\n/g' html/*.html
	perl -i -p -0 -e 's/(<div class="code">\n*)(\n<br\/>\n)+/\1/g' html/*.html

html/toc.html: toc.md
	markdown $< | cat toc-header.html - toc-footer.html > $@

rmhtml: html
	rm -f html/toc.html html/coqdoc.css

html/coqdoc.css: coqdoc.css
	cp $< $@

html/Symbola.woff: Symbola.woff
	cp $< $@
