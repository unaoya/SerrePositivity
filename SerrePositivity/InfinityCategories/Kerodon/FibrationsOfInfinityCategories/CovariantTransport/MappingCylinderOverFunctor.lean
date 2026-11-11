module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PushoutFunctorColimits
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Connected

/-!
概要：終域を固定した写像円柱の関手と連結な余極限の保存。
方針：円柱部分と共通の終域の射を pushout で貼り、点ごとの pushout と余極限の可換性を使う。
規約：通常の単体集合の余極限のみを扱う。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、写像円柱比較の始域のセル分解への自然性。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：同じ終域への射の間の可換な射が写像円柱の射を誘導する。
方針：円柱部分に区間と左成分の直積を使い、共通の終域は恒等射で保つ。
規約：Over S の射 u の可換条件を貼り合わせに使う。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、セルの包含による写像円柱の比較。 -/
noncomputable def mappingCylinderOverMap {S : SSet.{u}} {A B : Over S} (u : A ⟶ B) :
    pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A.left) A.hom ⟶ pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B.left) B.hom :=
  pushout.desc (((Δ[1] : SSet.{u}) ◁ u.left) ≫ pushout.inl _ _) (pushout.inr _ _) (by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, pushout.condition,
      ← Category.assoc, u.w])

/-- 概要：写像円柱の誘導射は円柱部分で区間と左成分の直積に一致する。
方針：pushout の左包含の計算則を使う。
規約：共通の終域は S。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、写像円柱比較の自然性の円柱部分。 -/
lemma mappingCylinderOverMap_inl {S : SSet.{u}} {A B : Over S} (u : A ⟶ B) :
    pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A.left) A.hom ≫ mappingCylinderOverMap u =
      ((Δ[1] : SSet.{u}) ◁ u.left) ≫ pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B.left) B.hom :=
  pushout.inl_desc _ _ _

/-- 概要：写像円柱の誘導射は共通の終域を保つ。
方針：pushout の右包含の計算則を使う。
規約：終域の成分は恒等射で写す。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、写像円柱比較の自然性の終域部分。 -/
lemma mappingCylinderOverMap_inr {S : SSet.{u}} {A B : Over S} (u : A ⟶ B) :
    pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A.left) A.hom ≫ mappingCylinderOverMap u =
      pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B.left) B.hom := pushout.inr_desc _ _ _

/-- 概要：Over の恒等射は写像円柱の恒等射を誘導する。
方針：円柱と終域の両包含で比較する。
規約：貼り合わせ射そのものの等式を結論する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、写像円柱関手の単位則。 -/
lemma mappingCylinderOverMap_id {S : SSet.{u}} (A : Over S) :
    mappingCylinderOverMap (𝟙 A) = 𝟙 (pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A.left) A.hom) := by
  apply pushout.hom_ext
  · rw [mappingCylinderOverMap_inl]
    change ((Δ[1] : SSet.{u}) ◁ 𝟙 A.left) ≫ _ = _ ≫ 𝟙 _
    rw [whiskerLeft_id, Category.id_comp, Category.comp_id]
  · rw [mappingCylinderOverMap_inr, Category.comp_id]

/-- 概要：Over の射の合成は写像円柱の誘導射の合成になる。
方針：円柱部分では直積の合成則、終域部分では固定条件を使う。
規約：u の後に v を合成する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、写像円柱関手の合成則。 -/
lemma mappingCylinderOverMap_comp {S : SSet.{u}} {A B C : Over S}
    (u : A ⟶ B) (v : B ⟶ C) :
    mappingCylinderOverMap (u ≫ v) = mappingCylinderOverMap u ≫ mappingCylinderOverMap v := by
  apply pushout.hom_ext
  · rw [mappingCylinderOverMap_inl, ← Category.assoc, mappingCylinderOverMap_inl,
      Category.assoc, mappingCylinderOverMap_inl, ← Category.assoc, ← whiskerLeft_comp]
    rfl
  · rw [mappingCylinderOverMap_inr, ← Category.assoc, mappingCylinderOverMap_inr,
      mappingCylinderOverMap_inr]

/-- 概要：終域を固定した写像円柱の関手。
方針：Over の対象の構造射の写像円柱を取り、可換な射を pushout の誘導射へ写す。
規約：始域は通常の圏 Over S。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、始域のセル分解の写像円柱への作用。 -/
noncomputable def mappingCylinderOverFunctor (S : SSet.{u}) : Over S ⥤ SSet.{u} where
  obj A := pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A.left) A.hom
  map u := mappingCylinderOverMap u
  map_id A := mappingCylinderOverMap_id A
  map_comp u v := mappingCylinderOverMap_comp u v

/-- 概要：始域から円柱部分への終端包含は Over S 上で自然。
方針：prism の終端の自然性を使う。
規約：円柱では区間を左因子に取る。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、点ごとの pushout の最初の射。 -/
noncomputable def mappingCylinderEndpointNat (S : SSet.{u}) :
    Over.forget S ⟶ Over.forget S ⋙ tensorLeft (Δ[1] : SSet.{u}) where
  app A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A.left
  naturality _ _ u := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality 1 u.left).symm

/-- 概要：Over S の構造射は忘却関手から S の定値関手への自然変換。
方針：Over の射の可換条件を使う。
規約：各対象の成分はその構造射そのもの。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、点ごとの pushout の二つ目の射。 -/
def mappingCylinderStructureNat (S : SSet.{u}) :
    Over.forget S ⟶ (CategoryTheory.Functor.const (Over S)).obj S where
  app A := A.hom
  naturality A B u := by
    change u.left ≫ B.hom = A.hom ≫ 𝟙 S
    simpa only [Category.comp_id] using u.w

/-- 概要：円柱部分の包含は終域を固定した写像円柱に自然。
方針：誘導射の円柱部分での式を使う。
規約：始域の関手は忘却と区間との直積の合成。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、点ごとの pushout の左の包含。 -/
noncomputable def mappingCylinderInlNat (S : SSet.{u}) :
    Over.forget S ⋙ tensorLeft (Δ[1] : SSet.{u}) ⟶ mappingCylinderOverFunctor S where
  app A := pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A.left) A.hom
  naturality _ _ u := (mappingCylinderOverMap_inl u).symm

/-- 概要：共通の終域の包含は終域を固定した写像円柱に自然。
方針：誘導射の終域部分での式を使う。
規約：定値関手の射の作用は恒等射。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、点ごとの pushout の右の包含。 -/
noncomputable def mappingCylinderInrNat (S : SSet.{u}) :
    (CategoryTheory.Functor.const (Over S)).obj S ⟶ mappingCylinderOverFunctor S where
  app A := pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A.left) A.hom
  naturality A B u := by
    change 𝟙 S ≫ pushout.inr _ _ = pushout.inr _ _ ≫ mappingCylinderOverMap u
    rw [Category.id_comp]
    exact (mappingCylinderOverMap_inr u).symm

/-- 概要：終域を固定した写像円柱の関手は連結な形の余極限を保つ。
方針：忘却・区間との直積・定値関手の余極限保存を点ごとの pushout で貼る。
規約：単体集合の形 J の余極限の存在を要求する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、境界の pushout と骨格の余極限の比較。 -/
instance mappingCylinderOverFunctor_preservesColimitsOfShape (S : SSet.{u})
    (J : Type*) [Category* J] [IsConnected J] [HasColimitsOfShape J SSet.{u}] :
    PreservesColimitsOfShape J (mappingCylinderOverFunctor S) := by
  haveI : PreservesColimitsOfShape J ((CategoryTheory.Functor.const (Over S)).obj S) :=
    ⟨fun {F} ↦ ⟨fun {c} _ ↦ ⟨by
      exact isColimitConstCocone J S⟩⟩⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.preservesColimitsOfShape_of_pointwise_pushout J (mappingCylinderEndpointNat S)
    (mappingCylinderStructureNat S) (mappingCylinderInlNat S) (mappingCylinderInrNat S)
    (fun A ↦ IsPushout.of_hasPushout _ _)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
