all: RndClose.vo RndTrapdoor.vo

Posrat.vo:
	coqc Posrat.v

Meas.vo: Posrat.vo
	coqc Meas.v

Expansion.vo: Meas.vo Posrat.vo
	coqc Expansion.v

PIOA.vo: Expansion.vo Meas.vo Posrat.vo
	coqc PIOA.v

RndTrapdoor.vo: PIOA.vo Meas.vo
	coqc RndTrapdoor.v

RndClose.vo: PIOA.vo Meas.vo
	coqc RndClose.v

