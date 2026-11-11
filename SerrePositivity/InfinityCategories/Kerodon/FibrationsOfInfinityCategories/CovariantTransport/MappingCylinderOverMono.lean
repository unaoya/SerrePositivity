module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.MappingCylinderOverFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PushoutMonoCube

/-!
概要：終域を固定した写像円柱の単射保存。
方針：prism の端点の自然性が pullback であることを pushout の単射判定に使う。
規約：構造射自体には単射性を要求しない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、セルの包含に沿う比較の貼り合わせ。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：prism の端点を係数に射影すると恒等射になる。
方針：直積の第二射影の計算を使う。
規約：時刻 i は任意。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、端点の単射性。 -/
lemma prismEndpoint_snd (i : Fin 2) (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i A ≫ snd (Δ[1] : SSet.{u}) A = 𝟙 A := rfl

/-- 概要：prism の端点包含は単射。
方針：係数への射影が左逆になることを使う。
規約：全ての単体集合と両端点に適用する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、写像円柱の貼り合わせ辺。 -/
instance prismEndpoint_mono (i : Fin 2) (A : SSet.{u}) : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i A) := by
  exact mono_of_mono_fac (prismEndpoint_snd i A)

/-- 概要：prism の端点の自然性の正方形は pullback。
方針：係数への射影から持ち上げを取り、時刻成分が定値であることを使う。
規約：係数の射 f は任意。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、写像円柱の比較の単射判定。 -/
lemma isPullback_prismEndpoint_naturality (i : Fin 2) {A B : SSet.{u}} (f : A ⟶ B) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i A) f ((Δ[1] : SSet.{u}) ◁ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i B) := by
  apply IsPullback.mk' (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality i f)
  · intro T a b h₁ h₂
    simpa only [Category.assoc, prismEndpoint_snd, Category.comp_id] using
      h₁ =≫ snd (Δ[1] : SSet.{u}) A
  · intro T a b h
    refine ⟨a ≫ snd (Δ[1] : SSet.{u}) A, ?_, ?_⟩
    · apply CartesianMonoidalCategory.hom_ext
      · have he := h =≫ fst (Δ[1] : SSet.{u}) B
        simpa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, Category.assoc] using he.symm
      · simp only [Category.assoc, prismEndpoint_snd, Category.comp_id]
    · simpa only [Category.assoc, whiskerLeft_snd, prismEndpoint_snd,
        Category.comp_id] using h =≫ snd (Δ[1] : SSet.{u}) B

/-- 概要：底上の単射は写像円柱の単射を誘導する。
方針：端点の自然性の pullback を pushout の単射判定に適用する。
規約：底 S の成分は恒等射。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、単射に沿う比較の貼り合わせ。 -/
instance mappingCylinderOverMap_mono {S : SSet.{u}} {A B : Over S}
    (u : A ⟶ B) [Mono u.left] : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderOverMap u) := by
  have : Mono ((Δ[1] : SSet.{u}) ◁ u.left) := (tensorLeft _).map_mono _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mono_of_pushout_cube (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _)
    u.left ((Δ[1] : SSet.{u}) ◁ u.left) (𝟙 S) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderOverMap u)
    (isPullback_prismEndpoint_naturality 1 u.left)
    (by simpa only [Category.comp_id] using u.w.symm)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderOverMap_inl u)
    (by simpa only [Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderOverMap_inr u)

/-- 概要：終域を固定した写像円柱関手は単射を保つ。
方針：Over の単射の左成分が単射であることを使う。
規約：単射性は通常の圏の意味。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、セル分解に沿う比較の帰納。 -/
instance mappingCylinderOverFunctor_preservesMonomorphisms (S : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderOverFunctor S).PreservesMonomorphisms where
  preserves u _ := mappingCylinderOverMap_mono u

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
