LEC_DIR := ../EE546_W25/Lectures/
BUILD_DIR := ./build

SOURCES := SL2.lean

SOURCES     := $(wildcard $(SOURCES)/*.md) 

all: $(SOURCES)
	python ./dm.py $(LEC_DIR)/$@ > $(BUILD_DIR)/$@
