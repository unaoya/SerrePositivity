module

public import SerrePositivity.KST.DerivedGeometry.ComplexDiagramTranspose
public import SerrePositivity.KST.DerivedGeometry.ShortComplexPointwiseExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
概要：完全な余極限は非有界複体の非輪状性を保つ。
方針：図式を関手圏内の複体へ転置し、完全な余極限関手を項別に適用する。
規約：非輪状性の存在を未証明条件として追加しない。
使われ方：Stacks Lemma 19.12.4・Theorem 19.12.6、TT §3・§8、Toën §3.2 の対象族の付加と超限工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {J C : Type*} [Category* J] [Category* C] [Abelian C]
  {ι : Type*} (c : ComplexShape ι)

/--
概要：非輪状な複体の図式を転置した関手圏内の複体も非輪状。
方針：短複体の完全性を各評価で判定する。
規約：図式の余極限はまだ使わない。
使われ方：Stacks Theorem 19.12.6、TT §3 の極限での非輪状性。
-/
lemma complexDiagramTranspose_acyclic (F : J ⥤ HomologicalComplex C c)
    (hF : ∀ j, (F.obj j).Acyclic) : (complexDiagramTranspose c F).Acyclic := by
  intro n
  apply shortComplex_exact_of_evaluation
  intro j
  change (F.obj j).ExactAt n
  exact hF j n

/--
概要：完全な J 型余極限は非輪状な複体の図式の非輪状性を保つ。
方針：完全な colim 関手で転置複体を写し、実際の複体の余極限と同型で比較する。
規約：複体の次数の上下限は不要。
使われ方：Stacks Lemma 19.12.4・Theorem 19.12.6、TT §3・§8 の非有界分解の極限。
-/
lemma acyclic_colimit_of_exactColimits [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
    (F : J ⥤ HomologicalComplex C c) (hF : ∀ j, (F.obj j).Acyclic) :
    (colimit F).Acyclic := by
  have ht := complexDiagramTranspose_acyclic c F hF
  have hm : (((colim : (J ⥤ C) ⥤ C).mapHomologicalComplex c).obj
      (complexDiagramTranspose c F)).Acyclic := fun n => (ht n).map (colim : (J ⥤ C) ⥤ C)
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hm n).isZero_homology.of_iso
    ((HomologicalComplex.homologyFunctor C c n).mapIso (colimitComplexTransposeIso c F))

end SerrePositivity.KST.DerivedGeometry
