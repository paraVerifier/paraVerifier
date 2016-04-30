
INCLUDEPATH = src


main: mutualEx.ml mesi.ml moesi.ml germanish.ml german.ml flash.ml
	corebuild mutualEx.byte -I ${INCLUDEPATH} -pkg re2
	corebuild mesi.byte -I ${INCLUDEPATH} -pkg re2
	corebuild moesi.byte -I ${INCLUDEPATH} -pkg re2
	corebuild germanish.byte -I ${INCLUDEPATH} -pkg re2
	corebuild german.byte -I ${INCLUDEPATH} -pkg re2
	corebuild flash.byte -I ${INCLUDEPATH} -pkg re2

clean:
	rm -rf _build
	rm *.byte
