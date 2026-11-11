module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentInterior

/-!
# coherent 単体から dg 単体の成分族への比較

概要：coherent 単体の頂点と全ての有限頂点集合の立方体評価から dg 単体の成分族を作る。
方針：頂点集合を native な ULift の順序へ移し、両端を除いた有限内部点を評価する。
規約：このファイルでは SimplexData を作り、dg 方程式と単体的自然性は後続で証明する。
使われ方：HA Construction 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の比較写像の各次数の台データ。

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

/-- 概要：coherent 単体を dg 単体の頂点と斉次成分の族へ送る。
方針：各有限頂点集合の最小・最大の間の立方体を降順に評価する。
規約：始域の native な頂点は ULift、標的の頂点番号は Fin。方程式はまだ課さない。
使われ方：HA 1.3.1.16 の比較写像の単体データの定義。 -/
def coherentSimplexData {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n := by
  let F : EnrichedFunctor SSet (SimplicialThickening (ULift.{u} (Fin (n + 1))))
    (ClosedCategory R D) := s
  refine { obj := fun a ↦ F.obj (.mk (ULift.up a)), hom := ?_ }
  intro I a b k hI ha hb hk
  have hamin : IsLeast (I : Set (Fin (n + 1))) a := by
    rw [ha]
    exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (n + 1))) b := by
    rw [hb]
    exact I.isGreatest_max' _
  have hab : a < b := by
    rw [ha, hb]
    exact I.min'_lt_max'_of_card (by omega)
  let U := I.image (ULift.up : Fin (n + 1) → ULift.{u} (Fin (n + 1)))
  have haU : IsLeast (U : Set (ULift.{u} (Fin (n + 1)))) (ULift.up a) := by
    constructor
    · exact Finset.mem_image.mpr ⟨a, hamin.1, rfl⟩
    · intro z hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
      exact hamin.2 ht
  have hbU : IsGreatest (U : Set (ULift.{u} (Fin (n + 1)))) (ULift.up b) := by
    constructor
    · exact Finset.mem_image.mpr ⟨b, hbmax.1, rfl⟩
    · intro z hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
      exact hbmax.2 ht
  have habU : (ULift.up a : ULift.{u} (Fin (n + 1))) < ULift.up b := hab
  have hcard : U.card = I.card := Finset.card_image_of_injective _
    (fun _ _ h ↦ congrArg ULift.down h)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt F habU (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet U (ULift.up a) (ULift.up b)) k (by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_coherentInteriorSet haU hbU habU
    rw [hcard] at h
    omega)

/-- 概要：coherent 単体の頂点は元の豊穣関手の同じ頂点である。
方針：単体データの対象成分を評価する。
規約：Fin の頂点を ULift した native な頂点へ移す。
使われ方：Kerodon 2.5.9（Tag 00SC） の比較写像の頂点上の一致。 -/
lemma coherentSimplexData_obj {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌) (a : Fin (n + 1)) :
    (coherentSimplexData s).obj a = s.obj (.mk (ULift.up a)) := rfl

/-- 概要：比較単体データの各成分は内部点の標準立方体評価と異種等号で一致する。
方針：次数を指定した成分の定義と標準成分への異種等号を使う。
規約：次数は 2−|I|、内部点の次数表示は負の内部点数。
使われ方：HA 1.3.1.16 の dg 方程式と単体的自然性の証明への入口。 -/
lemma coherentSimplexData_hom_heq {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)) :
    HEq ((coherentSimplexData s).hom I a b k hI ha hb hk)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent s
        (show (ULift.up a : ULift.{u} (Fin (n + 1))) < ULift.up b by
          change a < b
          rw [ha, hb]
          exact I.min'_lt_max'_of_card (by omega))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet (I.image (ULift.up : Fin (n + 1) → ULift.{u} (Fin (n + 1))))
          (ULift.up a) (ULift.up b))) := by
  unfold coherentSimplexData
  dsimp only
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt_heq _ _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
