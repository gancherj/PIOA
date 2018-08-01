all: RndClose.vo RndTrapdoor.vo

Posrat.vo: Posrat.v
	coqc Posrat.v

Meas.vo: Posrat.vo Meas.v
	coqc Meas.v

Expansion.vo: Meas.vo Posrat.vo Expansion.v Lems.vo
	coqc Expansion.v

PIOA.vo: Expansion.vo Meas.vo Posrat.vo PIOA.v Lems.vo
	coqc PIOA.v

RndTrapdoor.vo: PIOA.vo Meas.vo RndTrapdoor.v Lems.vo
	coqc RndTrapdoor.v

RndClose.vo: PIOA.vo Meas.vo RndClose.v Lems.vo
	coqc RndClose.v

Lems.vo : Lems.v
	coqc Lems.v
