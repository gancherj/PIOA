all: RndClose.vo RndTrapdoor.vo

Posrat.vo: Posrat.v
	coqc Posrat.v

Meas.vo: Posrat.vo Meas.v
	coqc Meas.v

Expansion.vo: Meas.vo Posrat.vo Expansion.v
	coqc Expansion.v

PIOA.vo: Expansion.vo Meas.vo Posrat.vo PIOA.v
	coqc PIOA.v

RndTrapdoor.vo: PIOA.vo Meas.vo RndTrapdoor.v
	coqc RndTrapdoor.v

RndClose.vo: PIOA.vo Meas.vo RndClose.v
	coqc RndClose.v

