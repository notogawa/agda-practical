.PHONY: clean

uniq: example/uniq.agda
	agda -c -i. -i/usr/share/agda-stdlib/ $<

clean:
	$(RM) uniq
	$(RM) -rf MAlonzo
