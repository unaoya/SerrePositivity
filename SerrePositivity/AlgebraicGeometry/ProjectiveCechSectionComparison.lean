module

public import SerrePositivity.AlgebraicGeometry.ProjectiveProjCechSectionAlgebraEquiv
public import SerrePositivity.AlgebraicGeometry.CechAlgebraNonemptyEqualizerEquiv
public import SerrePositivity.AlgebraicGeometry.ReesClosedHomogeneousSections
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechSectionAlgebra

/-!
概要：斉次局所化の適合切断代数と、実際の Proj の適合切断代数を同定する。
方針：非空交叉の自然な代数同型を適合切断に適用する。
規約：基底環のスカラーと積は実際の標準開への写像で保つ。
使われ方：F7 の有限切断代数の四角形と閉厚化の Frobenius 比較を接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 標準開の斉次局所化と Proj の構造層から作る適合切断代数の同型。
BST13 Lemma 3.8・3.9 の H⁰ の計算に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveCechSectionAlgebraEquiv :
    projectiveHomogeneousSectionAlgebra (ι := ι) G ≃ₐ[R]
      projectiveCechSectionAlgebra (ι := ι) G :=
  fullAlgebraCechNonemptyEqualizerEquiv
    (projectiveProjCechSectionAlgEquiv G)
    (fun hT h x ↦ projectiveProjCechSectionAlgEquiv_naturality G hT h x)

/-- 適合切断代数の比較の各成分は、実際の標準開の切断への比較。 -/
theorem projectiveCechSectionAlgebraEquiv_apply
    (a : projectiveHomogeneousSectionAlgebra (ι := ι) G) (t : Fin 1 → ι) :
    (projectiveCechSectionAlgebraEquiv G a).val t =
      projectiveProjCechSectionAlgEquiv G (cechTupleSupport t)
        (cechTupleSupport_nonempty t) (a.val t) := rfl

/-- 切断代数の比較は、四角形の増大写像である基底スカラーを保つ。 -/
theorem projectiveCechSectionAlgebraEquiv_algebraMap (r : R) :
    projectiveCechSectionAlgebraEquiv (ι := ι) G (algebraMap R _ r) =
      algebraMap R _ r :=
  (projectiveCechSectionAlgebraEquiv G).commutes r

end SerrePositivity.AlgebraicGeometry
