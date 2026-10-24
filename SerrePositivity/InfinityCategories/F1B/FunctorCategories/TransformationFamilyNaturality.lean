module

public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.TransformationFamilies
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalFunctorMap

/-!
概要：非定値端点の族の展開の二つの変数と標的に関する自然性。
方針：区間模型の関手性、内部 Hom の前後合成、座標交換を照合する。
規約：関手の変数 A と族の変数 B を区別する。
使われ方：点ごとの写像空間条件を自然変換の族へ移すための整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：非定値端点の族の展開は族のパラメータの前合成に自然。
方針：区間模型の前合成、uncurry と座標交換の自然性を使う。
規約：関手 U,V の変数 A は固定。
使われ方：部分族への制限。 -/
lemma transformationFamilyUncurry_precomp {A B C X : SSet.{u}} {U V : A ⟶ X}
    (i : B ⟶ C) (f : C ⟶ intervalMappingSpace (functorVertex U) (functorVertex V)) :
    transformationFamilyUncurry (i ≫ f) =
      (Δ[1] ◁ (A ◁ i)) ≫ transformationFamilyUncurry f := by
  unfold transformationFamilyUncurry
  rw [intervalMappingUncurry_precomp, uncurry_natural_left,
    ← Category.assoc, ← intervalParameterSwap_naturality, Category.assoc]

/-- 概要：非定値端点の族の展開は標的の関手に自然。
方針：区間模型の後合成の公式と uncurry の自然性を使う。
規約：U,V は U≫F,V≫F へ写る。
使われ方：随伴の右関手が自然変換の族に与える作用。 -/
lemma transformationFamilyUncurry_postcomp {A B X Y : SSet.{u}} {U V : A ⟶ X}
    (f : B ⟶ intervalMappingSpace (functorVertex U) (functorVertex V)) (F : X ⟶ Y) :
    transformationFamilyUncurry (U := U ≫ F) (V := V ≫ F)
      (f ≫ intervalFunctorMap ((ihom A).map F) (functorVertex U) (functorVertex V)) =
      transformationFamilyUncurry f ≫ F := by
  unfold transformationFamilyUncurry
  rw [intervalFunctorMap_uncurry, uncurry_natural_right, Category.assoc]

/-- 概要：非定値端点の族の展開は関手の始域の制限に自然。
方針：内部 Hom の pre による作用を uncurry し、A の座標交換と照合する。
規約：制限後の端点は i≫U,i≫V。
使われ方：一般のパラメータ付き Hom 対応の前合成自然性。 -/
lemma transformationFamilyUncurry_restrict {A A' B X : SSet.{u}} {U V : A ⟶ X}
    (i : A' ⟶ A) (f : B ⟶ intervalMappingSpace (functorVertex U) (functorVertex V)) :
    transformationFamilyUncurry (U := i ≫ U) (V := i ≫ V)
      (f ≫ intervalFunctorMap ((pre i).app X) (functorVertex U) (functorVertex V)) =
      (Δ[1] ◁ (i ▷ B)) ≫ transformationFamilyUncurry f := by
  unfold transformationFamilyUncurry
  rw [intervalFunctorMap_uncurry, uncurry_pre_app]
  have hc : intervalParameterSwap A' B ≫ (i ▷ (Δ[1] ⊗ B)) =
      (Δ[1] ◁ (i ▷ B)) ≫ intervalParameterSwap A B := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  rw [← Category.assoc, hc, Category.assoc]

/-- 概要：族のホモトピーの射は標的の後合成と可換。
方針：展開の標的自然性を区間交換の後で使う。
規約：標準区間は第二因子。
使われ方：自然変換を右関手に送った場合の計算。 -/
lemma transformationFamilyHomotopy_postcomp {A B X Y : SSet.{u}} {U V : A ⟶ X}
    (f : B ⟶ intervalMappingSpace (functorVertex U) (functorVertex V)) (F : X ⟶ Y) :
    (transformationFamilyHomotopy (U := U ≫ F) (V := V ≫ F)
      (f ≫ intervalFunctorMap ((ihom A).map F) (functorVertex U) (functorVertex V))).h =
      (transformationFamilyHomotopy f).h ≫ F := by
  change (β_ (A ⊗ B) (Δ[1] : SSet.{u})).hom ≫ _ = _
  rw [transformationFamilyUncurry_postcomp]
  rfl

/-- 概要：族のホモトピーの射はパラメータ B の前合成と可換。
方針：展開の前合成自然性と対称性の自然性を使う。
規約：関手の変数 A は固定。
使われ方：部分族のホモトピーの制限。 -/
lemma transformationFamilyHomotopy_precomp {A B C X : SSet.{u}} {U V : A ⟶ X}
    (i : B ⟶ C) (f : C ⟶ intervalMappingSpace (functorVertex U) (functorVertex V)) :
    (transformationFamilyHomotopy (i ≫ f)).h =
      ((A ◁ i) ▷ (Δ[1] : SSet.{u})) ≫ (transformationFamilyHomotopy f).h := by
  change (β_ (A ⊗ B) (Δ[1] : SSet.{u})).hom ≫ _ = _
  rw [transformationFamilyUncurry_precomp]
  have hc : (β_ (A ⊗ B) (Δ[1] : SSet.{u})).hom ≫ (Δ[1] ◁ (A ◁ i)) =
      ((A ◁ i) ▷ (Δ[1] : SSet.{u})) ≫ (β_ (A ⊗ C) (Δ[1] : SSet.{u})).hom := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  rw [← Category.assoc, hc, Category.assoc]
  rfl

/-- 概要：族のホモトピーの射は関手の変数 A の制限と可換。
方針：展開の制限自然性と対称性の自然性を使う。
規約：族の変数 B は固定。
使われ方：非定値関手 U,V の前合成の計算。 -/
lemma transformationFamilyHomotopy_restrict {A A' B X : SSet.{u}} {U V : A ⟶ X}
    (i : A' ⟶ A) (f : B ⟶ intervalMappingSpace (functorVertex U) (functorVertex V)) :
    (transformationFamilyHomotopy (U := i ≫ U) (V := i ≫ V)
      (f ≫ intervalFunctorMap ((pre i).app X) (functorVertex U) (functorVertex V))).h =
      ((i ▷ B) ▷ (Δ[1] : SSet.{u})) ≫ (transformationFamilyHomotopy f).h := by
  change (β_ (A' ⊗ B) (Δ[1] : SSet.{u})).hom ≫ _ = _
  rw [transformationFamilyUncurry_restrict]
  have hc : (β_ (A' ⊗ B) (Δ[1] : SSet.{u})).hom ≫ (Δ[1] ◁ (i ▷ B)) =
      ((i ▷ B) ▷ (Δ[1] : SSet.{u})) ≫ (β_ (A ⊗ B) (Δ[1] : SSet.{u})).hom := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  rw [← Category.assoc, hc, Category.assoc]
  rfl

end SerrePositivity.InfinityCategories
