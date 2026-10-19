module

public import SerrePositivity.InfinityCategories.F1.FiberTransportFamily

/-!
概要：輸送族のパラメーターと始点の係数の変更。
方針：一つの持ち上げた prism を前合成し、関手空間への射の厳密な自然性を得る。
規約：持ち上げを選び直さない。
使われ方：Kerodon Lemma 5.6.9.1、両端の fiber 同値を指定した輸送の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：輸送族はパラメーターの任意の射で制限できる。
方針：終点と prism の両方に同じ射を前合成する。
規約：始点の係数射を厳密に保つ。
使われ方：高次単体や一本の辺への普遍輸送の制限。 -/
def FiberTransportFamily.precomp {E B K L M : SSet.{u}} {p : E ⟶ B}
    {a b : B _⦋0⦌} {f : K ⟶ vertexFiber p a} {γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B}
    (T : FiberTransportFamily (b := b) p f γ) (h : M ⟶ L) :
    FiberTransportFamily (b := b) p f ((Δ[1] ◁ h) ≫ γ) where
  endpoint := (K ◁ h) ≫ T.endpoint
  prism := (Δ[1] ◁ (K ◁ h)) ≫ T.prism
  start := by
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, T.start,
      ← Category.assoc, whiskerLeft_fst]
  finish := by
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, T.finish,
      Category.assoc]
  over_base := by
    rw [Category.assoc, T.over_base, ← Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, whiskerLeft_snd,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- 概要：輸送族の制限は写像空間への射の厳密な前合成と一致する。
方針：curry のパラメーターに関する自然性を使う。
規約：同型ではなく射の等式。
使われ方：普遍輸送の各単体と指定パラメーターへの評価。 -/
lemma FiberTransportFamily.precomp_map {E B K L M : SSet.{u}} {p : E ⟶ B}
    {a b : B _⦋0⦌} {f : K ⟶ vertexFiber p a} {γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B}
    (T : FiberTransportFamily (b := b) p f γ) (h : M ⟶ L) :
    (T.precomp h).map = h ≫ T.map := by
  exact curry_natural_left _ _

/-- 概要：輸送族は始点 fiber への係数射の前合成と整合する。
方針：係数変数で prism と終点を同時に引き戻す。
規約：底のパラメーター付きの辺の族を変えない。
使われ方：指定した fiber 同値を始点に持つ普遍輸送。 -/
def FiberTransportFamily.precomposeSource {E B K K' L : SSet.{u}} {p : E ⟶ B}
    {a b : B _⦋0⦌} {f : K ⟶ vertexFiber p a} {γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B}
    (T : FiberTransportFamily (b := b) p f γ) (h : K' ⟶ K) :
    FiberTransportFamily (b := b) p (h ≫ f) γ where
  endpoint := (h ▷ L) ≫ T.endpoint
  prism := (Δ[1] ◁ (h ▷ L)) ≫ T.prism
  start := by
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, T.start,
      ← Category.assoc, whiskerRight_fst, Category.assoc]
    simp only [Category.assoc]
  finish := by
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, T.finish,
      Category.assoc]
  over_base := by
    rw [Category.assoc, T.over_base, ← Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, whiskerRight_snd]

/-- 概要：始点の係数の変更は写像空間の前合成作用と厳密に一致する。
方針：curry の定義域側の自然性を使う。
規約：高次パラメーター全体での等式。
使われ方：Kerodon Lemma 5.6.9.1、始点の fiber 同値を前合成する比較。 -/
lemma FiberTransportFamily.precomposeSource_map {E B K K' L : SSet.{u}} {p : E ⟶ B}
    {a b : B _⦋0⦌} {f : K ⟶ vertexFiber p a} {γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B}
    (T : FiberTransportFamily (b := b) p f γ) (h : K' ⟶ K) :
    (T.precomposeSource h).map = T.map ≫ (pre h).app (vertexFiber p b) := by
  apply uncurry_injective
  change uncurry (curry ((h ▷ L) ≫ T.endpoint)) =
    uncurry (curry T.endpoint ≫ (pre h).app (vertexFiber p b))
  rw [uncurry_pre_app, uncurry_curry, uncurry_curry]

end SerrePositivity.InfinityCategories
