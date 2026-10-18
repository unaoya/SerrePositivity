import SerrePositivity.KST.ProExcision
/-!
概要：K-L6 が所有する公開宣言の型と公理を監査する。
方針：各宣言を #check @ と #print axioms で確認する。
規約：標準三公理 propext・Classical.choice・Quot.sound のみを許す。
使われ方：KST §4・App. A の各保存単位。未完了の工程を証明済みとはしない。
-/
set_option pp.universes true
set_option pp.explicit true

#check @SerrePositivity.KST.ProExcision.Tower
#print axioms SerrePositivity.KST.ProExcision.Tower

#check @SerrePositivity.KST.ProExcision.Tower.constant
#print axioms SerrePositivity.KST.ProExcision.Tower.constant

#check @SerrePositivity.KST.ProExcision.Tower.map
#print axioms SerrePositivity.KST.ProExcision.Tower.map

#check @SerrePositivity.KST.ProExcision.LevelHom
#print axioms SerrePositivity.KST.ProExcision.LevelHom

#check @SerrePositivity.KST.ProExcision.LevelHom.id
#print axioms SerrePositivity.KST.ProExcision.LevelHom.id

#check @SerrePositivity.KST.ProExcision.LevelHom.comp
#print axioms SerrePositivity.KST.ProExcision.LevelHom.comp

#check @SerrePositivity.KST.ProExcision.LevelHom.map
#print axioms SerrePositivity.KST.ProExcision.LevelHom.map

#check @SerrePositivity.KST.ProExcision.IsProIso
#print axioms SerrePositivity.KST.ProExcision.IsProIso

#check @SerrePositivity.KST.ProExcision.IsProIso.id
#print axioms SerrePositivity.KST.ProExcision.IsProIso.id

#check @SerrePositivity.KST.ProExcision.IsProIso.map
#print axioms SerrePositivity.KST.ProExcision.IsProIso.map

#check @SerrePositivity.KST.ProExcision.IsProIso.comp
#print axioms SerrePositivity.KST.ProExcision.IsProIso.comp

#check @SerrePositivity.KST.ProExcision.IsProIso.constant_inverse
#print axioms SerrePositivity.KST.ProExcision.IsProIso.constant_inverse

#check @SerrePositivity.KST.ProExcision.diagonal_cofinal
#print axioms SerrePositivity.KST.ProExcision.diagonal_cofinal

#check @SerrePositivity.KST.ProExcision.Tower.reindex
#print axioms SerrePositivity.KST.ProExcision.Tower.reindex

#check @SerrePositivity.KST.ProExcision.Tower.reindexHom
#print axioms SerrePositivity.KST.ProExcision.Tower.reindexHom

#check @SerrePositivity.KST.ProExcision.Tower.reindexHom_isProIso
#print axioms SerrePositivity.KST.ProExcision.Tower.reindexHom_isProIso

#check @SerrePositivity.KST.ProExcision.IsProZero
#print axioms SerrePositivity.KST.ProExcision.IsProZero

#check @SerrePositivity.KST.ProExcision.IsProZero.map
#print axioms SerrePositivity.KST.ProExcision.IsProZero.map

#check @SerrePositivity.KST.ProExcision.IsProZero.reindex
#print axioms SerrePositivity.KST.ProExcision.IsProZero.reindex

#check @SerrePositivity.KST.ProExcision.IsProEquivalence
#print axioms SerrePositivity.KST.ProExcision.IsProEquivalence

#check @SerrePositivity.KST.ProExcision.IsProCartesian
#print axioms SerrePositivity.KST.ProExcision.IsProCartesian

#check @SerrePositivity.KST.ProExcision.Tower.transition_apply
#print axioms SerrePositivity.KST.ProExcision.Tower.transition_apply

#check @SerrePositivity.KST.ProExcision.LevelHom.naturality_apply
#print axioms SerrePositivity.KST.ProExcision.LevelHom.naturality_apply

#check @SerrePositivity.KST.ProExcision.IsProMono
#print axioms SerrePositivity.KST.ProExcision.IsProMono

#check @SerrePositivity.KST.ProExcision.IsProEpi
#print axioms SerrePositivity.KST.ProExcision.IsProEpi

#check @SerrePositivity.KST.ProExcision.IsProIso.isProMono
#print axioms SerrePositivity.KST.ProExcision.IsProIso.isProMono

#check @SerrePositivity.KST.ProExcision.IsProIso.isProEpi
#print axioms SerrePositivity.KST.ProExcision.IsProIso.isProEpi

#check @SerrePositivity.KST.ProExcision.descendRange
#print axioms SerrePositivity.KST.ProExcision.descendRange

#check @SerrePositivity.KST.ProExcision.descendRange_apply
#print axioms SerrePositivity.KST.ProExcision.descendRange_apply

#check @SerrePositivity.KST.ProExcision.isProIso_of_mono_epi
#print axioms SerrePositivity.KST.ProExcision.isProIso_of_mono_epi

#check @SerrePositivity.KST.ProExcision.FiveTerm
#print axioms SerrePositivity.KST.ProExcision.FiveTerm

#check @SerrePositivity.KST.ProExcision.FiveTermHom
#print axioms SerrePositivity.KST.ProExcision.FiveTermHom

#check @SerrePositivity.KST.ProExcision.FiveTermHom.isProMono
#print axioms SerrePositivity.KST.ProExcision.FiveTermHom.isProMono

#check @SerrePositivity.KST.ProExcision.FiveTermHom.isProEpi
#print axioms SerrePositivity.KST.ProExcision.FiveTermHom.isProEpi

#check @SerrePositivity.KST.ProExcision.FiveTermHom.isProIso
#print axioms SerrePositivity.KST.ProExcision.FiveTermHom.isProIso

#check @SerrePositivity.KST.ProExcision.LevelwiseExactSequence
#print axioms SerrePositivity.KST.ProExcision.LevelwiseExactSequence

#check @SerrePositivity.KST.ProExcision.ExactTowerSequence
#print axioms SerrePositivity.KST.ProExcision.ExactTowerSequence

#check @SerrePositivity.KST.ProExcision.LevelwiseExactSequence.toTower
#print axioms SerrePositivity.KST.ProExcision.LevelwiseExactSequence.toTower

#check @SerrePositivity.KST.ProExcision.ExactTowerSequence.fiveTerm
#print axioms SerrePositivity.KST.ProExcision.ExactTowerSequence.fiveTerm

