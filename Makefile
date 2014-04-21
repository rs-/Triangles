COQDOCFLAGS?=-interpolate -utf8 -s --with-header assets/coq-header.html --with-footer assets/coq-footer.html
-include Makefile.coq

Makefile.coq:
	coq_makefile -f Make -o $@

doc: rmhtml html/toc.html html/coqdoc.css html/Symbola.woff html/jquery-1.11.0.min.js
	perl -i assets/alignment.pl html/*.html
	sed -i'.bk' -f assets/replace.sed html/*.html
	perl -i -p -0 -e 's/(\n<br\/>\n)+/<br\/>\n/g' html/*.html
	perl -i -p -0 -e 's/(<div class="code">\n*)(\n<br\/>\n)+/\1/g' html/*.html
	rm -rf html/*.bk

html/toc.html: toc.md
	markdown $< | cat assets/toc-header.html - assets/toc-footer.html > $@

rmhtml: html
	rm -f html/toc.html html/coqdoc.css

html/%: assets/%
	cp $< $@
