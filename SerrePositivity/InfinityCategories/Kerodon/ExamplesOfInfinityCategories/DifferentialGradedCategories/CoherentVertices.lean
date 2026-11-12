module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentLowComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful

/-!
# 比較写像の頂点と本質的全射性

概要：各 dg 対象から定値 coherent 単体を作り、比較写像が零単体上全射であることを示す。
方針：全 Hom を dg 単位の定数単体に送り、既存の頂点と対象の同値を使う。
規約：coherent nerve の通常の圏構造は閉零射の圏とする。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の比較の本質的全射性と写像空間の端点。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：全ての対象と射を一つの dg 対象とその単位に送る coherent 単体。
方針：豊穣 Hom 写像を定数の単位写像にし、AW の単位則で合成保存を示す。
規約：全ての次元で同じ構成を使う。
使われ方：Kerodon 2.5.9（Tag 00SC） の coherent nerve の標準の頂点。 -/
def coherentConstant (x : D) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌ where
  obj _ := x
  map _ _ :=
    { app := fun m ↦ ↾fun _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := R) x m.unop.len
      naturality := by
        intro m n α
        apply ConcreteCategory.hom_ext
        intro _
        exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant_pullback (unitElement R x) α.unop.toOrderHom).symm }
  map_id _ := by
    apply CategoryTheory.NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro _
    rfl
  map_comp _ _ _ := by
    apply CategoryTheory.NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro _
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW_unit_left (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := R) x m.unop.len)).symm

/-- 概要：dg 対象を coherent nerve の零単体として表す。
方針：その対象の定値 coherent 単体を零次元で取る。
規約：対象の宇宙と係数環の宇宙を同一視しない。
使われ方：HA 1.3.1.17 の本質的全射性と pinched Hom の固定端点。 -/
def coherentVertex (x : D) : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) _⦋0⦌ :=
  coherentConstant x 0

/-- 概要：標準の coherent 頂点の比較像は同じ対象の dg 頂点である。
方針：対象成分を比較し、零単体の射族の一意性を使う。
規約：頂点の等式でありホモトピー類だけの一致ではない。
使われ方：Kerodon 2.5.9（Tag 00SC） の二つの写像空間の端点の同定。 -/
lemma coherentComparison_vertex (x : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison.app (Opposite.op ⦋0⦌) (coherentVertex (R := R) x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_hom_heq _ _

/-- 概要：比較写像は零単体上で全射である。
方針：標的の零単体に対応する dg 対象の標準 coherent 頂点を取る。
規約：標的の全ての零単体に対して厳密な原像を与える。
使われ方：HA 1.3.1.17 の比較の本質的全射性。 -/
lemma coherentComparison_surjective_vertices :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D)).app (Opposite.op ⦋0⦌)) := by
  intro t
  refine ⟨coherentVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv t), ?_⟩
  exact (coherentComparison_vertex _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.left_inv t)

/-- 概要：比較写像は Core の意味で本質的全射である。
方針：各標的頂点の厳密な原像を取り、その像と標的の恒等同型を使う。
規約：写像空間の充満忠実性はこの補題の仮定にも結論にも含めない。
使われ方：HA 1.3.1.17 の A3e の同値判定の本質的全射側。 -/
lemma coherentComparison_essentiallySurjective :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D)) := by
  intro t
  obtain ⟨x, hx⟩ := coherentComparison_surjective_vertices (R := R) t
  refine ⟨x, ?_⟩
  rw [hx]
  exact ⟨Iso.refl _⟩

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
