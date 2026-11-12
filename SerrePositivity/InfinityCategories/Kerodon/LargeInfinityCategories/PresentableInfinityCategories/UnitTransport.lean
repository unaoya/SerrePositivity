module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.UnitMappingFibers

/-!
概要：関手の可逆な比較に沿い、指定単位を保持して随伴を移送する。
方針：単位が誘導する全パラメータの Hom 写像を、元の随伴の対応と同型で分解する。
規約：移送後の随伴の存在は仮定せず構成する。
使われ方：実単位の対応の頂点条件の同型不変性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Bicategory
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：左一胞体の同型に沿う単位の移送は Hom 全単射を与える。
方針：左一胞体の同型による Hom 全単射と元の随伴の対応を合成する。
規約：双圏の任意のパラメータ一胞体について成立する。
使われ方：指定単位を持つ左関手の変更。 -/
lemma bicategoryUnitHomMap_changeLeft_bijective {B : Type u} [Bicategory.{w, v} B]
    {b c : B} {L L' : b ⟶ c} {R : c ⟶ b} (a : Bicategory.Adjunction L R)
    (i : L ≅ L') {d : B} (U : d ⟶ b) (V : d ⟶ c) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategoryUnitHomMap (a.unit ≫ i.hom ▷ R) U V) := by
  let e : (U ≫ L' ⟶ V) ≃ (U ⟶ V ≫ R) :=
    (Iso.homCongr (whiskerLeftIso U i.symm) (Iso.refl V)).trans a.homEquiv₂
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategoryUnitHomMap (a.unit ≫ i.hom ▷ R) U V = e := by
    funext α
    dsimp [e, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategoryUnitHomMap, Bicategory.Adjunction.homEquiv₂,
      Iso.homCongr, whiskerLeftIso]
    rw [Category.comp_id]
    bicategory
  rw [he]
  exact e.bijective

/-- 概要：左一胞体の同型に沿って元の随伴を移送する。
方針：移送した単位の全パラメータの Hom 全単射による判定を使う。
規約：右一胞体は元のものを使う。
使われ方：普遍単位の左関手の同型による変更。 -/
def bicategoryAdjunctionChangeLeft {B : Type u} [Bicategory.{w, v} B]
    {b c : B} {L L' : b ⟶ c} {R : c ⟶ b} (a : Bicategory.Adjunction L R)
    (i : L ≅ L') : Bicategory.Adjunction L' R :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategoryAdjunctionOfUnitHomBijective (a.unit ≫ i.hom ▷ R)
    (fun U V ↦ bicategoryUnitHomMap_changeLeft_bijective a i U V)

/-- 概要：左関手を変更して構成した随伴の単位は指定した移送単位。
方針：全パラメータ Hom 判定の単位回収公式を適用する。
規約：二胞体の厳密な等式。
使われ方：coslice 内の単位の可換条件との照合。 -/
lemma bicategoryAdjunctionChangeLeft_unit {B : Type u} [Bicategory.{w, v} B]
    {b c : B} {L L' : b ⟶ c} {R : c ⟶ b} (a : Bicategory.Adjunction L R)
    (i : L ≅ L') : (bicategoryAdjunctionChangeLeft a i).unit = a.unit ≫ i.hom ▷ R :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategoryAdjunctionOfUnitHomBijective_unit _ _

/-- 概要：右一胞体の同型に沿う単位の移送は Hom 全単射を与える。
方針：元の随伴の対応と右一胞体の同型による Hom 全単射を合成する。
規約：双圏の任意のパラメータ一胞体について成立する。
使われ方：指定単位を持つ右関手の変更。 -/
lemma bicategoryUnitHomMap_changeRight_bijective {B : Type u} [Bicategory.{w, v} B]
    {b c : B} {L : b ⟶ c} {R R' : c ⟶ b} (a : Bicategory.Adjunction L R)
    (i : R ≅ R') {d : B} (U : d ⟶ b) (V : d ⟶ c) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategoryUnitHomMap (a.unit ≫ L ◁ i.hom) U V) := by
  let e : (U ≫ L ⟶ V) ≃ (U ⟶ V ≫ R') :=
    a.homEquiv₂.trans (Iso.homCongr (Iso.refl U) (whiskerLeftIso V i))
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategoryUnitHomMap (a.unit ≫ L ◁ i.hom) U V = e := by
    funext α
    dsimp [e, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategoryUnitHomMap, Bicategory.Adjunction.homEquiv₂,
      Iso.homCongr, whiskerLeftIso]
    rw [Category.id_comp]
    simp only [Bicategory.whiskerLeft_comp, Category.assoc]
    rw [Bicategory.associator_inv_naturality_right_assoc]
    rw [← Bicategory.whisker_exchange]
  rw [he]
  exact e.bijective

/-- 概要：右一胞体の同型に沿って元の随伴を移送する。
方針：移送した単位の全パラメータの Hom 全単射による判定を使う。
規約：左一胞体は元のものを使う。
使われ方：普遍単位の右関手の同型による変更。 -/
def bicategoryAdjunctionChangeRight {B : Type u} [Bicategory.{w, v} B]
    {b c : B} {L : b ⟶ c} {R R' : c ⟶ b} (a : Bicategory.Adjunction L R)
    (i : R ≅ R') : Bicategory.Adjunction L R' :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategoryAdjunctionOfUnitHomBijective (a.unit ≫ L ◁ i.hom)
    (fun U V ↦ bicategoryUnitHomMap_changeRight_bijective a i U V)

/-- 概要：右関手を変更して構成した随伴の単位は指定した移送単位。
方針：全パラメータ Hom 判定の単位回収公式を適用する。
規約：二胞体の厳密な等式。
使われ方：coslice 内の単位の可換条件との照合。 -/
lemma bicategoryAdjunctionChangeRight_unit {B : Type u} [Bicategory.{w, v} B]
    {b c : B} {L : b ⟶ c} {R R' : c ⟶ b} (a : Bicategory.Adjunction L R)
    (i : R ≅ R') : (bicategoryAdjunctionChangeRight a i).unit = a.unit ≫ L ◁ i.hom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategoryAdjunctionOfUnitHomBijective_unit _ _

open MonoidalClosed SSet
local instance unitTransportHomCategory (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

/-- 概要：元の関手圏の同型を QCat の二胞体の同型に戻す。
方針：二胞体の表示の両逆で hom・inv を戻し、忠実性で逆則を反映する。
規約：同じ二つの元の関手を両端とする。
使われ方：元の関手圏上の随伴単位の移送。 -/
def qcatIsoOfFunctorIso {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    {L L' : C ⟶ D} (i : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso L L') : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap L ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap L' where
  hom := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv L L').symm i.hom
  inv := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv L' L).symm i.inv
  hom_inv_id := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor C D).map_injective
    exact i.hom_inv_id
  inv_hom_id := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor C D).map_injective
    exact i.inv_hom_id

/-- 概要：元の関手圏の左関手の同型に沿って随伴を構成する。
方針：関手同型を二胞体の同型に戻し、指定単位の移送を適用する。
規約：新たな随伴の存在を仮定しない。
使われ方：随伴単位の全部分空間の頂点条件の照合。 -/
def qcatAdjunctionChangeLeft {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    {L L' : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R) (i : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso L L') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L' R :=
  bicategoryAdjunctionChangeLeft a (qcatIsoOfFunctorIso i)

/-- 概要：元の関手圏の右関手の同型に沿って随伴を構成する。
方針：関手同型を二胞体の同型に戻し、指定単位の移送を適用する。
規約：新たな随伴の存在を仮定しない。
使われ方：随伴単位の全部分空間の頂点条件の照合。 -/
def qcatAdjunctionChangeRight {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    {L : C ⟶ D} {R R' : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R) (i : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso R R') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R' :=
  bicategoryAdjunctionChangeRight a (qcatIsoOfFunctorIso i)

/-- 概要：左関手の変更は、元の単位に左比較の右関手による像を続ける。
方針：二胞体の単位移送を元の h Fun の表示と右 whisker の公式で読む。
規約：元の全関手圏の射の等式。
使われ方：実単位の可換三角形による頂点条件の移送。 -/
lemma qcatAdjunctionChangeLeft_unitHom {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    {L L' : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R) (i : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso L L') :
    (qcatAdjunctionChangeLeft a i).unitHom = a.unitHom ≫
      (hoFunctor.map ((ihom C).map R)).toFunctor.map i.hom := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (bicategoryAdjunctionChangeLeft a (qcatIsoOfFunctorIso i)).unit = _
  rw [bicategoryAdjunctionChangeLeft_unit]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor C C).map (a.unit ≫ (qcatIsoOfFunctorIso i).hom ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap R) = _
  rw [CategoryTheory.Functor.map_comp]
  change a.unitHom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ ((qcatIsoOfFunctorIso i).hom ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap R) = _
  exact congrArg (a.unitHom ≫ ·) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerRight (qcatIsoOfFunctorIso i).hom R)

/-- 概要：右関手の変更は、元の単位に右比較の左関手による前合成を続ける。
方針：二胞体の単位移送を元の h Fun の表示と左 whisker の公式で読む。
規約：元の全関手圏の射の等式。
使われ方：実単位の可換三角形による頂点条件の移送。 -/
lemma qcatAdjunctionChangeRight_unitHom {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    {L : C ⟶ D} {R R' : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R) (i : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso R R') :
    (qcatAdjunctionChangeRight a i).unitHom = a.unitHom ≫
      (hoFunctor.map ((pre L).app C)).toFunctor.map i.hom := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (bicategoryAdjunctionChangeRight a (qcatIsoOfFunctorIso i)).unit = _
  rw [bicategoryAdjunctionChangeRight_unit]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor C C).map (a.unit ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap L ◁ (qcatIsoOfFunctorIso i).hom) = _
  rw [CategoryTheory.Functor.map_comp]
  change a.unitHom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap L ◁ (qcatIsoOfFunctorIso i).hom) = _
  exact congrArg (a.unitHom ≫ ·) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerLeft L (qcatIsoOfFunctorIso i).hom)

/-- 概要：単位の写像空間条件は左関手の可逆な比較に沿って移送できる。
方針：元の指定単位の随伴を構成し、移送した随伴の単位条件を回収する。
規約：単位の像の式を指定し、任意の単位への変更はしない。
使われ方：随伴単位の全部分空間の頂点条件の不変性。 -/
lemma unitMappingSpaceCondition_changeLeft {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    {L L' : C ⟶ D} {R : D ⟶ C} {η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 C) (L ≫ R)}
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η) (i : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso L L') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition (η ≫ (hoFunctor.map ((ihom C).map R)).toFunctor.map i.hom) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.unitMappingSpaceCondition
    (qcatAdjunctionChangeLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatAdjunctionOfUnitMappingSpaceCondition η hη) i)
  rw [qcatAdjunctionChangeLeft_unitHom, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatAdjunctionOfUnitMappingSpaceCondition_unitHom] at h
  exact h

/-- 概要：単位の写像空間条件は右関手の可逆な比較に沿って移送できる。
方針：元の指定単位の随伴を構成し、移送した随伴の単位条件を回収する。
規約：単位の像の式を指定し、任意の単位への変更はしない。
使われ方：随伴単位の全部分空間の頂点条件の不変性。 -/
lemma unitMappingSpaceCondition_changeRight {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    {L : C ⟶ D} {R R' : D ⟶ C} {η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 C) (L ≫ R)}
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η) (i : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso R R') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition (η ≫ (hoFunctor.map ((pre L).app C)).toFunctor.map i.hom) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.unitMappingSpaceCondition
    (qcatAdjunctionChangeRight (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatAdjunctionOfUnitMappingSpaceCondition η hη) i)
  rw [qcatAdjunctionChangeRight_unitHom, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatAdjunctionOfUnitMappingSpaceCondition_unitHom] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
