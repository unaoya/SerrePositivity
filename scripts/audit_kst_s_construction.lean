import SerrePositivity.KST.SConstruction

/-!
概要：S• 構成の公開宣言の型と公理を監査する。
方針：各宣言を #check / #print axioms で検査する。
規約：propext・Classical.choice・Quot.sound のみ許可。
使われ方：BGT §7 に対応する保存単位の検証。
-/

#check @SerrePositivity.KST.SConstruction.Ar
#print axioms SerrePositivity.KST.SConstruction.Ar
#check @SerrePositivity.KST.SConstruction.arObj
#print axioms SerrePositivity.KST.SConstruction.arObj
#check @SerrePositivity.KST.SConstruction.arMap
#print axioms SerrePositivity.KST.SConstruction.arMap
#check @SerrePositivity.KST.SConstruction.arMap_id
#print axioms SerrePositivity.KST.SConstruction.arMap_id
#check @SerrePositivity.KST.SConstruction.arMap_comp
#print axioms SerrePositivity.KST.SConstruction.arMap_comp
#check @SerrePositivity.KST.SConstruction.arNerve
#print axioms SerrePositivity.KST.SConstruction.arNerve
#check @SerrePositivity.KST.SConstruction.arNerveMap
#print axioms SerrePositivity.KST.SConstruction.arNerveMap
#check @SerrePositivity.KST.SConstruction.arNerveMap_id
#print axioms SerrePositivity.KST.SConstruction.arNerveMap_id
#check @SerrePositivity.KST.SConstruction.arNerveMap_comp
#print axioms SerrePositivity.KST.SConstruction.arNerveMap_comp
#check @SerrePositivity.KST.SConstruction.diagramSpace
#print axioms SerrePositivity.KST.SConstruction.diagramSpace
#check @SerrePositivity.KST.SConstruction.intervalStep
#print axioms SerrePositivity.KST.SConstruction.intervalStep
#check @SerrePositivity.KST.SConstruction.intervalStep_le
#print axioms SerrePositivity.KST.SConstruction.intervalStep_le
#check @SerrePositivity.KST.SConstruction.le_intervalStep
#print axioms SerrePositivity.KST.SConstruction.le_intervalStep
#check @SerrePositivity.KST.SConstruction.arSquareOrder
#print axioms SerrePositivity.KST.SConstruction.arSquareOrder
#check @SerrePositivity.KST.SConstruction.arSquare
#print axioms SerrePositivity.KST.SConstruction.arSquare
#check @SerrePositivity.KST.SConstruction.IsGapped
#print axioms SerrePositivity.KST.SConstruction.IsGapped
#check @SerrePositivity.KST.SConstruction.arSquare_naturality
#print axioms SerrePositivity.KST.SConstruction.arSquare_naturality
#check @SerrePositivity.KST.SConstruction.IsGapped.precomp
#print axioms SerrePositivity.KST.SConstruction.IsGapped.precomp
#check @SerrePositivity.KST.SConstruction.gappedSubcomplex
#print axioms SerrePositivity.KST.SConstruction.gappedSubcomplex
#check @SerrePositivity.KST.SConstruction.sConstruction
#print axioms SerrePositivity.KST.SConstruction.sConstruction
#check @SerrePositivity.KST.SConstruction.sConstruction_quasicategory
#print axioms SerrePositivity.KST.SConstruction.sConstruction_quasicategory
#check @SerrePositivity.KST.SConstruction.sMap
#print axioms SerrePositivity.KST.SConstruction.sMap
#check @SerrePositivity.KST.SConstruction.sMap_ι
#print axioms SerrePositivity.KST.SConstruction.sMap_ι
#check @SerrePositivity.KST.SConstruction.sMap_id
#print axioms SerrePositivity.KST.SConstruction.sMap_id
#check @SerrePositivity.KST.SConstruction.sMap_comp
#print axioms SerrePositivity.KST.SConstruction.sMap_comp
#check @SerrePositivity.KST.SConstruction.simplicialSConstruction
#print axioms SerrePositivity.KST.SConstruction.simplicialSConstruction
