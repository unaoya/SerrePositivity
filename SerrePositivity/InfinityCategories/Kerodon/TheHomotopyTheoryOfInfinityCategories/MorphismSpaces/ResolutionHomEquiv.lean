module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ResolutionHomReindex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.FlagEquiv

/-!
# pinched 単体と解像からの Hom 射の同値

概要：本比較の旗での評価を F1 の両側の逆を持つ構成に同定する。
方針：端点の表示と native Path の集合の表示を等式で合わせる。
規約：固定次数の型の同値であり、比較射のホモトピー同値とは区別する。
使われ方：HA 1.3.1.17、Kerodon Corollary 4.6.7.16（Tag 01LQ） の写像空間の解像による表示。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：本比較の pinched 単体と F1 の端点表示を持つ単体は同値である。
方針：端点の等式を pinched 条件に合成し、台の単体を保つ。
規約：全ての次数で同じ台の coherent 単体を使う。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ） の F1 の同値の適用。 -/
def resolutionEndpointEquiv (x y : ClosedCategory R D) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedHom (R := R) (D := D) x y) _⦋n⦌ ≃
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y) n where
  toFun s :=
    { val := s.val
      source := s.source.trans (congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z n)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentNerveVertex_eq_vertex x).symm)
      target := s.target.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentNerveVertex_eq_vertex y).symm }
  invFun s :=
    { val := s.val
      source := s.source.trans (congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z n)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentNerveVertex_eq_vertex x))
      target := s.target.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentNerveVertex_eq_vertex y) }
  left_inv s := by apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext; rfl
  right_inv s := by apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext; rfl

/-- 概要：本比較の旗の Path の単体は F1 の旗の Path の単体に等しい。
方針：各段の集合の所属を持ち上げの単射性で比較する。
規約：同じ native Path の二つの集合表示を等式で同定する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ） の確定済みの逆構成への接続。 -/
lemma resolutionFlagPathFunctor_eq_pathFlag {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPathFunctor.{u} F = F.pathFlag := by
  refine CategoryTheory.Functor.ext (fun t ↦ ?_)
  apply SimplicialThickening.Path.ext
  apply Set.ext
  intro z
  change (z = ULift.up (Fin.last (n + 1)) ∨
    ∃ j ∈ F.sets t, ULift.up j.castSucc = z) ↔
      (z.down = Fin.last (n + 1) ∨ ∃ j ∈ F.sets t, z.down = j.castSucc)
  constructor
  · rintro (h | ⟨j, hj, h⟩)
    · exact Or.inl (congrArg ULift.down h)
    · exact Or.inr ⟨j, hj, (congrArg ULift.down h).symm⟩
  · rintro (h | ⟨j, hj, h⟩)
    · exact Or.inl (ULift.ext h)
    · exact Or.inr ⟨j, hj, ULift.ext h.symm⟩

/-- 概要：本比較の解像からの射は端点を合わせた F1 の旗の射に等しい。
方針：各旗で Path の単体の一致を適用し、端点の証明の差を消す。
規約：全次数の単体集合の射の等式。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ） の両側の逆の本比較への移送。 -/
lemma resolutionHomMap_eq_flagMap {x y : ClosedCategory R D} {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedHom (R := R) (D := D) x y) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionHomMap s = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPinchedFlagMap (resolutionEndpointEquiv x y n s) := by
  apply CategoryTheory.NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro F
  change (s.val.map _ _ ≫ eqToHom _).app d (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPathFunctor F.down) =
    (s.val.map _ _ ≫ eqToHom _).app d F.down.pathFlag
  rw [resolutionFlagPathFunctor_eq_pathFlag]

/-- 概要：固定次数の coherent pinched 単体は解像から標準 Hom への射と同値である。
方針：端点の表示の同値と F1 の旗の写像の同値を合成する。
規約：局所 Kan 性を追加の前提としない。
使われ方：HA 1.3.1.17 の反対側の合成を解像上で扱うための逆構成。 -/
def resolutionHomEquiv (x y : ClosedCategory R D) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedHom (R := R) (D := D) x y) _⦋n⦌ ≃
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y) :=
  (resolutionEndpointEquiv x y n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPinchedFlagEquiv x y n)

/-- 概要：構成した型の同値の順方向は実際の解像上の評価である。
方針：F1 の射への同定を型の同値の定義へ適用する。
規約：同値が存在するだけでなく、既存の射を回収する等式。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ） の逆性を自然性のある評価に適用する。 -/
lemma resolutionHomEquiv_apply (x y : ClosedCategory R D) (n : ℕ)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedHom (R := R) (D := D) x y) _⦋n⦌) :
    resolutionHomEquiv x y n s = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionHomMap s :=
  (resolutionHomMap_eq_flagMap s).symm

/-- 概要：解像上の射を pinched 単体に戻して評価すると元の射を回収する。
方針：構成した同値の右逆則を実際の評価へ移す。
規約：単体集合の射の厳密な等式。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ） の解像側の回収則。 -/
lemma resolutionHomMap_equiv_symm {x y : ClosedCategory R D} {n : ℕ}
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionHomMap ((resolutionHomEquiv x y n).symm φ) = φ := by
  rw [← resolutionHomEquiv_apply]
  exact (resolutionHomEquiv x y n).apply_symm_apply φ

/-- 概要：pinched 単体を解像上で評価して逆構成すると元の単体を回収する。
方針：同値の左逆則を既存の評価へ移す。
規約：台の単体の全ての豊穣 Hom を含めた等式。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ） の pinched 側の回収則。 -/
lemma resolutionHomEquiv_symm_map {x y : ClosedCategory R D} {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedHom (R := R) (D := D) x y) _⦋n⦌) :
    (resolutionHomEquiv x y n).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionHomMap s) = s := by
  rw [← resolutionHomEquiv_apply]
  exact (resolutionHomEquiv x y n).symm_apply_apply s

/-- 概要：解像上の射からの逆構成も pinched 次数の変更と可換である。
方針：順方向の単射性と自然性により逆構成の二つの値を比較する。
規約：任意の面・退化に対する厳密な等式。
使われ方：HA 1.3.1.17 の解像による表示を単体的な比較に使う。 -/
lemma resolutionHomEquiv_symm_reindex {x y : ClosedCategory R D} {m n : ℕ}
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y)
    (β : ⦋m⦌ ⟶ ⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedHom (R := R) (D := D) x y).map β.op
        ((resolutionHomEquiv x y n).symm φ) =
      (resolutionHomEquiv x y m).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap β.toOrderHom ≫ φ) := by
  apply (resolutionHomEquiv x y m).injective
  simp only [resolutionHomEquiv_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionHomMap_reindex, resolutionHomMap_equiv_symm]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
