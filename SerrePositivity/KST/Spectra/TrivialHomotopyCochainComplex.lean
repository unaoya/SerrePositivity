module

public import SerrePositivity.KST.Spectra.TrivialHomotopyLinearCochains
public import SerrePositivity.KST.Spectra.AlternatingCofaceFunctorIso
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
概要：自明な Kan 作用の高次 π_* の cochain complex と線形係数の cochain complex の比較。
方針：余単体の加法的同型を交代余面複体へ送り、忘却との交換同型を合成する。
規約：係数の加群構造を指定する。Tot のホモトピー群を計算する主張は含まない。
使われ方：Goerss–Jardine VIII §2。有理係数の cohomology の消滅を高次 π_* の複体へ移す。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet

namespace SerrePositivity.KST.Spectra.TrivialHomotopyCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : PointedSimplicialSet.{u}) [KanComplex X.right]
    (R G : Type u) [CommRing R] [Group G]

local instance trivialComplexUnderlyingKan : KanComplex (Action.trivial G X).V.right :=
  inferInstanceAs (KanComplex X.right)

/-- 概要：高次 π_* の加法的 cochain complex は線形係数の複体の忘却と同型。
方針：余単体図式の比較と加法関手の交代余面複体との交換を合成する。
規約：q はホモトピー次数 q+2、複体の次数は別の自然数。
使われ方：Goerss–Jardine VIII §2。代数的な cohomology の消滅を適用する実際の複体比較。 -/
def complexIso (q : ℕ) [Module R (coefficient X q)] :
    KanHomotopyGroup.cochainComplex (PointedActionCochains.obj (Action.trivial G X)) q ≅
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (LinearGroupCochains.complex (Rep.trivial R G (coefficient X q))) :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).mapIso
      (linearDiagramIso X R G q) ≪≫
    ((alternatingCofaceFunctorIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).app
      (linearDiagram X R G q)).symm

/-- 概要：加群から加法群への忘却は cochain complex のコホモロジーと可換。
方針：各次数の短複体の homology 保存の実際の比較同型を使う。
規約：通常の加群圏の核・余核の保存による同型。
使われ方：Goerss–Jardine VIII §2。線形係数のコホモロジーを加法群へ戻す。 -/
def forgetHomologyIso (C : CochainComplex (ModuleCat.{u} R) ℕ) (s : ℕ) :
    (((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj C).homology s ≅
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj (C.homology s) :=
  (C.sc s).mapHomologyIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

/-- 概要：高次 π_* の cochain のコホモロジーは線形係数のコホモロジーの加法群と同型。
方針：複体の実際の比較に homology を施し、加群忘却の比較を合成する。
規約：全複体次数 s で成立する。
使われ方：Goerss–Jardine VIII §2。有理平均化の結果を π_* の cochain に接続する。 -/
def cohomologyIso (q : ℕ) [Module R (coefficient X q)] (s : ℕ) :
    (KanHomotopyGroup.cochainComplex
      (PointedActionCochains.obj (Action.trivial G X)) q).homology s ≅
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
        ((LinearGroupCochains.complex (Rep.trivial R G (coefficient X q))).homology s) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) s).mapIso
      (complexIso X R G q) ≪≫
    forgetHomologyIso R (LinearGroupCochains.complex (Rep.trivial R G (coefficient X q))) s

end

end SerrePositivity.KST.Spectra.TrivialHomotopyCochains
