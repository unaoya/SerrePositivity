module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentLowEvaluation

/-!
# 比較写像の辺と三角形

概要：実際の比較写像は辺の零成分と三角形の次数 −1 の成分を符号なしで保つ。
方針：二点集合の内部座標は空、三頂点全体の内部座標は中間点一つであることを使う。
規約：三角形の旗は直接辺から二辺の合成へ進む。
使われ方：HA 1.3.1.16–1.3.1.17、Kerodon 2.5.9（Tag 00SC） の低次の一致。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory CategoryTheory.SimplicialThickening DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：比較写像の各辺は二端点だけの Path の零成分である。
方針：二点集合の内部点数が零であることと零次立方体の評価を使う。
規約：任意次元の単体の任意の異なる二頂点に適用できる。
使われ方：Kerodon 2.5.9（Tag 00SC） の比較写像の辺での一致。 -/
lemma coherentComparison_edgeHom {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌)
    (a b : Fin (n + 1)) (hab : a < b) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison.app _ s).edgeHom a b hab =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) (D := D) (s.obj (.mk (ULift.up a)))
        (s.obj (.mk (ULift.up b))) 0
        ((s.map (.mk (ULift.up a)) (.mk (ULift.up b))).app (Opposite.op ⦋0⦌)
          ((CategoryTheory.Functor.const (Fin 1)).obj
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior (show (ULift.up a : ULift.{u} (Fin (n + 1))) <
              ULift.up b from hab) ∅))) := by
  have ha₀ : IsLeast (({a, b} : Finset _) : Set _) a := by
    refine ⟨by simp, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · rw [Finset.mem_singleton.mp hx]
      exact hab.le
  have hb₀ : IsGreatest (({a, b} : Finset _) : Set _) b := by
    refine ⟨by simp, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hab.le
    · exact (Finset.mem_singleton.mp hx).le
  have hS : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior.{u} {a, b} a b = ∅ := by
    apply Finset.card_eq_zero.mp
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior_card.{u} ha₀ hb₀ hab
    have hc : ({a, b} : Finset _).card = 2 := by simp [ne_of_lt hab]
    omega
  apply eq_of_heq
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData_hom_heq_set s {a, b} a b 0 _ _ _ _ hab ∅ hS).trans
  exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent_empty s _)

/-- 概要：三頂点の中間点を native な内部座標として取る。
方針：零番と二番の間に一番の頂点を置く。
規約：元の頂点番号と順序を保って宇宙だけを持ち上げる。
使われ方：HA 1.3.1.16 の三角形の次数 −1 の成分。 -/
def triangleCoordinate : Set.Ioo (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2) :=
  ⟨ULift.up 1, by decide, by decide⟩

/-- 概要：三頂点全体の内部座標は中間点だけである。
方針：Fin 3 の内部点の値は零より大きく二より小さいので一に等しい。
規約：部分型の所属証明を値の等式から同定する。
使われ方：Kerodon 2.5.9（Tag 00SC） の三角形と一次立方体の照合。 -/
lemma coherentVertexInterior_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior.{u} (Finset.univ : Finset (Fin 3)) 0 2 = {triangleCoordinate} := by
  ext z
  constructor
  · intro _
    apply Finset.mem_singleton.mpr
    apply Subtype.ext
    apply ULift.ext
    apply Fin.ext
    have hp := z.property
    change 0 < z.val.down.val ∧ z.val.down.val < 2 at hp
    change z.val.down.val = 1
    omega
  · intro _
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_coherentInteriorSet _ _ _ z).mpr
      (Finset.mem_image.mpr ⟨z.val.down, Finset.mem_univ _, rfl⟩)

/-- 概要：比較写像の三角形の高次成分は内部点を加える旗の一次成分である。
方針：既存 dg 単体の triangleHom を一点の内部座標の立方体評価に直す。
規約：旗は {0,2} から {0,1,2} へ進み、次数 −1 の値に負号は付かない。
使われ方：HA 1.3.1.16–1.3.1.17 の比較写像の二単体での一致。 -/
lemma coherentComparison_triangleHom
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) _⦋2⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison.app _ s).triangleHom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) (D := D) (s.obj (.mk (ULift.up 0)))
        (s.obj (.mk (ULift.up 2))) 1
        ((s.map (.mk (ULift.up 0)) (.mk (ULift.up 2))).app (Opposite.op ⦋1⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.singletonPathFlag (by decide) triangleCoordinate)) := by
  have hdeg : (-1 : ℤ) =
      -((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior.{u} (Finset.univ : Finset (Fin 3)) 0 2).card : ℤ) := by
    rw [coherentVertexInterior_triangle]
    simp
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData s).hom Finset.univ 0 2 (-1) _ _ _ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData_hom_eq_componentAt s Finset.univ 0 2 (-1) _ _ _ _ (by decide) hdeg]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt_eq_of_set_eq s (by decide) _ {triangleCoordinate} (-1)
    hdeg (by simp) coherentVertexInterior_triangle).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt_singleton s (by decide) triangleCoordinate)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
