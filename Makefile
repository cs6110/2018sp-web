.PHONY: build clean view serve deploy notes

build: node_modules notes
	rsync -tv notes/build/lectures/*.pdf src/lectures
	yarn run build

serve: node_modules
	yarn run serve

clean:
	rm -rf build

view:
	open build/index.html

node_modules: package.json
	yarn

notes:
	make -C notes


# Deployment.

RSYNCARGS := --compress --recursive --checksum --itemize-changes \
	--delete -e ssh --perms --chmod=Du=rwx,Dgo=rx,Fu=rw,Fog=r
DEST := cslinux:/courses/cs6110/2018sp

deploy: clean build
	rsync $(RSYNCARGS) build/ $(DEST)
