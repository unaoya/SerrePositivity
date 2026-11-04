module

public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
public import SerrePositivity.InfinityCategories.Core.Limit
public import SerrePositivity.InfinityCategories.Core.MappingSpaceRightKan
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.KanModels.KanPointHomNaturality
public import SerrePositivity.InfinityCategories.HomotopyLimits.AdjunctionHomLimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanConeLimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanSourceReplacement
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictCones
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictNerveMaps

/-!
概要：Kan 複体の積と内部 Hom の随伴に、極限保存用の単体的 Hom 同型を与える。
方針：閉構造の内部 curry を自然同型に束ね、零単体で通常の随伴と照合する。
規約：具体例は Quillen の単体集合であり、モデル構造の追加仮定は置かない。
使われ方：HTT 5.2.4.6、γ4 の frame 比較と cf 置換を含む入力の検証。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 二つの Kan 複体の積のホーンは成分ごとに充填できる。 -/
lemma kanTensor_isKan (K X : SSet.{u}) [KanComplex K] [KanComplex X] :
    KanComplex (K ⊗ X) := by
  apply kanComplex_of_rightHornFillers
  intro n i _ σ
  obtain ⟨a, ha⟩ := KanComplex.hornFilling (σ ≫ CartesianMonoidalCategory.fst K X)
  obtain ⟨b, hb⟩ := KanComplex.hornFilling (σ ≫ CartesianMonoidalCategory.snd K X)
  refine ⟨CartesianMonoidalCategory.lift a b, ?_⟩
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [Category.assoc, CartesianMonoidalCategory.lift_fst] using ha.symm
  · simpa only [Category.assoc, CartesianMonoidalCategory.lift_snd] using hb.symm

/-- Kan 複体との積。両因子の Kan 性から積も Kan になる。 -/
def kanTensorLeft (K : KanObject.{u}) : KanObject.{u} ⥤ KanObject.{u} where
  obj X := ⟨K.obj ⊗ X.obj, kanTensor_isKan K.obj X.obj⟩
  map f := K.obj ◁ f
  map_id X := by apply MonoidalCategory.whiskerLeft_id
  map_comp f g := by apply MonoidalCategory.whiskerLeft_comp

/-- Kan 複体への内部 Hom。始域の Kan 性は充填性に不要。 -/
def kanInternalHom (K : SSet.{u}) : KanObject.{u} ⥤ KanObject.{u} where
  obj Y := ⟨(ihom K).obj Y.obj, inferInstance⟩
  map f := (ihom K).map f
  map_id Y := (ihom K).map_id Y.obj
  map_comp f g := (ihom K).map_comp f g

/-- 閉構造の通常の随伴を Kan 複体へ制限する。 -/
def kanTensorAdjunction (K : KanObject.{u}) : kanTensorLeft K ⊣ kanInternalHom K.obj :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y ↦ (ihom.adjunction K.obj).homEquiv X.obj Y.obj
      homEquiv_naturality_left_symm := fun f g ↦
        (ihom.adjunction K.obj).homEquiv_naturality_left_symm f g
      homEquiv_naturality_right := fun f g ↦
        (ihom.adjunction K.obj).homEquiv_naturality_right f g }

/-- 内部 curry は終域の全単体で自然。 -/
lemma kanIhomCurry_naturality (K X : SSet.{u}) {Y Z : SSet.{u}} (f : Y ⟶ Z) :
    (ihom (K ⊗ X)).map f ≫ ihomCurry K X Z =
      ihomCurry K X Y ≫ (ihom X).map ((ihom K).map f) := by
  apply uncurry_injective
  apply uncurry_injective
  simp only [uncurry_natural_left, uncurry_uncurry_ihomCurry]
  rw [uncurry_ihom_map]
  rw [associator_inv_naturality_right_assoc, ← uncurry_eq, uncurry_ihom_map]
  rw [uncurry_natural_right]
  simpa only [uncurry_eq, MonoidalCategory.whiskerLeft_comp, Category.assoc] using
    congrArg (fun g ↦ g ≫ f) (uncurry_uncurry_ihomCurry K X Y).symm

/-- 内部 curry の零単体は通常の閉構造の curry と一致する。 -/
lemma kanIhomCurry_zero {K X Y : SSet.{u}} (f : K ⊗ X ⟶ Y) :
    curry' f ≫ ihomCurry K X Y = curry' (curry f) := by
  apply uncurry_injective
  apply uncurry_injective
  simp only [uncurry_natural_left, uncurry_uncurry_ihomCurry, curry', uncurry_curry]
  rw [associator_inv_naturality_right_assoc, ← uncurry_eq, uncurry_curry]
  simp

/-- 表現可能な豊穣 Hom の内部 curry 自然同型。 -/
def kanTensorHomNatIso (K X : KanObject.{u}) :
    (SimplicialCategory.sHomFunctor KanObject.{u}).obj (Opposite.op ((kanTensorLeft K).obj X)) ≅
      kanInternalHom K.obj ⋙
        (SimplicialCategory.sHomFunctor KanObject.{u}).obj (Opposite.op X) :=
  NatIso.ofComponents (fun Y ↦ ihomCurryIso K.obj X.obj Y.obj) (by
    intro Y Z f
    rw [kanObject_sHomWhiskerLeft]
    change (ihom (K.obj ⊗ X.obj)).map f ≫ ihomCurry K.obj X.obj Z.obj =
      ihomCurry K.obj X.obj Y.obj ≫ (ihom X.obj).map ((ihom K.obj).map f)
    exact kanIhomCurry_naturality K.obj X.obj f)

/-- 極限保存 API の入力。零単体では指定した通常の随伴に一致する。 -/
def kanTensorAdjunctionHomIso (K : KanObject.{u}) :
    SimplicialAdjunctionHomIso (kanTensorAdjunction K) := by
  refine ⟨kanTensorHomNatIso K, ?_⟩
  intro X Y f
  let f' : K.obj ⊗ X.obj ⟶ Y.obj := f
  change (ihomCurry K.obj X.obj Y.obj).app (Opposite.op ⦋0⦌)
    ((curry' f').app (Opposite.op ⦋0⦌) PUnit.unit) =
      (curry' (curry f')).app (Opposite.op ⦋0⦌) PUnit.unit
  exact congrArg (fun (g : 𝟙_ SSet.{u} ⟶ (ihom X.obj).obj ((ihom K.obj).obj Y.obj)) ↦
    g.app (Opposite.op ⦋0⦌) PUnit.unit) (kanIhomCurry_zero f')

/-- 任意の小さい strict 図式の ∞ 極限を、Kan 内部 Hom は保存する。 -/
lemma kanInternalHom_map_isLimit {I : Type u} [SmallCategory I]
    (K : KanObject.{u}) {F : I ⥤ KanObject.{u}} (c : Cone F)
    (hc : IsLimitCone (strictCoherentCone c)) :
    IsLimitCone (strictCoherentCone ((kanInternalHom K.obj).mapCone c)) :=
  strictCoherentCone_map_isLimit_of_adjunctionHomIso (kanTensorAdjunctionHomIso K) c hc

end
end SerrePositivity.InfinityCategories.HomotopyLimits
