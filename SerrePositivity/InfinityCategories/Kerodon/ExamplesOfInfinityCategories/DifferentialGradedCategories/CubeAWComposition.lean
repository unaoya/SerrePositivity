module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeBlockReindex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeSumDegenerate
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWCubeSum

/-!
# 立方体全体の AW 評価と dg 合成

概要：和の座標の二つの射影の AW 合成を全最大旗で評価すると、二つの立方体評価の dg 合成になる。
方針：区間を越える置換の旗を退化で消し、区間内置換の二重和へ再添字付けする。
規約：先頭の座標が後の射、末尾の座標が前の射。
使われ方：HA 1.3.1.16、Kerodon 2.5.8（Tag 00S0）–2.5.9（Tag 00SC） の合成面の基本鎖の評価。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y z : D}

/-- 概要：区間を越える置換の旗の AW 評価は零である。
方針：先頭・末尾を逆転する位置を検出し、その像の和の座標を求めて退化の消滅を使う。
規約：標準の連結番号付けを任意の全置換で置換する。
使われ方：Kerodon 2.5.8（Tag 00S0） の全旗の和から不適合な旗を消す。 -/
lemma standardTopEval_AW_cubeSum_zero_of_not_block {A B : Type u} {p q : ℕ}
    (e : Fin p ≃ A) (f : Fin q ≃ B) (σ : Equiv.Perm (Fin (p + q)))
    (hσ : σ ∉ Set.range (fun s : Equiv.Perm (Fin p) × Equiv.Perm (Fin q) ↦
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeBlockPermutation s.1 s.2))
    (ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) y z)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x z (p + q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW (ψ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumLeftMap A B).app _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f)))))
        (φ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumRightMap A B).app _
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f)))))) = 0 := by
  obtain ⟨r, s, hrs, hr, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeBlockPermutation_inversion_of_not_range σ hσ
  have hr' : ∃ b : B, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f) (σ r) = Sum.inr b := by
    cases h : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f) (σ r) with
    | inr b => exact ⟨b, rfl⟩
    | inl a =>
      have he := congrArg (fun t ↦ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f).symm t).val) h
      rw [Equiv.symm_apply_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration_symm_inl] at he
      have ha := (e.symm a).isLt
      change (σ r).val = (e.symm a).val at he
      omega
  have hs' : ∃ a : A, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f) (σ s) = Sum.inl a := by
    cases h : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f) (σ s) with
    | inl a => exact ⟨a, rfl⟩
    | inr b =>
      have he := congrArg (fun t ↦ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f).symm t).val) h
      rw [Equiv.symm_apply_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration_symm_inr] at he
      change (σ s).val = p + (f.symm b).val at he
      omega
  obtain ⟨b, hb⟩ := hr'
  obtain ⟨a, ha⟩ := hs'
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval_AW_cubeSum_zero_of_inversion
    (σ.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f)) r s hrs a b hb ha ψ φ

/-- 概要：全最大旗の AW 評価の符号付き和は二つの立方体評価の dg 合成である。
方針：区間外の置換の値を零にし、全置換の和を区間内置換の二重和に直す。
規約：p,q は任意で、零次元も含む。
使われ方：HA 1.3.1.16 の合成面の全ての旗の評価。 -/
lemma standardTopEval_AW_cubeSum_all_permutations {A B : Type u} {p q : ℕ}
    (e : Fin p ≃ A) (f : Fin q ≃ B)
    (ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) y z)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    (∑ σ : Equiv.Perm (Fin (p + q)), (Equiv.Perm.sign σ : ℤ) •
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x z (p + q)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW (ψ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumLeftMap A B).app _
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f)))))
          (φ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumRightMap A B).app _
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f))))))) =
      compose R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation e ψ) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation f φ) (by push_cast; omega) := by
  refine Eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeBlockPermutation_sum _ ?_) ?_
  · intro σ hσ
    rw [standardTopEval_AW_cubeSum_zero_of_not_block e f σ hσ ψ φ, smul_zero]
  · simp_rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeBlockPermutation_trans_enumeration]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval_AW_cubeSum_signed_sum e f ψ φ

/-- 概要：二つの座標射影の像を AW で合成する立方体の射を作る。
方針：前の射と後の射を Cartesian な積へ組み、標準 Hom の合成写像を適用する。
規約：積の第一因子が前の射、第二因子が後の射。
使われ方：Kerodon 2.5.9（Tag 00SC） の合成面の写像を評価する。 -/
def cubeAWCompositionMap {A B : Type u}
    (ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) y z)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube (A ⊕ B) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x z :=
  CartesianMonoidalCategory.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumRightMap A B ≫ φ) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumLeftMap A B ≫ ψ) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardComposition x y z

/-- 概要：二つの座標射影の AW 合成の立方体評価は二つの立方体評価の dg 合成である。
方針：立方体評価を全置換の和へ展開し、全旗の AW 評価の公式を使う。
規約：合成の終次数は −(p+q)。
使われ方：HA 1.3.1.16 の比較写像の合成項の鎖の等式。 -/
lemma cubeEvaluation_AW_comp {A B : Type u} {p q : ℕ}
    (e : Fin p ≃ A) (f : Fin q ≃ B)
    (ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) y z)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f) (cubeAWCompositionMap ψ φ) =
      compose R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation e ψ) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation f φ) (by push_cast; omega) := by
  exact standardTopEval_AW_cubeSum_all_permutations e f ψ φ

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
