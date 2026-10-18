module

public import SerrePositivity.KST.Spectra.RationalModuleLocalization
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
概要：アーベル群の乗法 telescope の圏論的余極限と ℚ テンソル。
方針：線形な乗法列を群の図式へ束ね、直極限の代表・等式で余極限性を証明する。
規約：群の加法記法を使う。スペクトルの telescope の比較は後に行う。
使われ方：BF 1978 §2、HA §1.4.2。L9d の整数次数群の有理化の計算。
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped TensorProduct

namespace SerrePositivity.KST.Spectra.RationalTelescope

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (A : Type u) [AddCommGroup A]

/-- 概要：乗法列をアーベル群の自然数図式として表す。
方針：各段を A とし、二段間の射を整数区間係数のスカラー写像とする。
規約：一段先の射は 2,3,4,… の乗法。
使われ方：HA §1.4.2。有理化の群の telescope 図式。 -/
def additiveDiagram : ℕ ⥤ AddCommGrpCat.{u} where
  obj _ := AddCommGrpCat.of A
  map {i j} f := AddCommGrpCat.ofHom (scalarTransition A i j (leOfHom f)).toAddMonoidHom
  map_id i := by
    ext a
    change integerCoefficient i i • a = a
    rw [integerCoefficient_self, one_smul]
  map_comp {i j k} f g := by
    ext a
    change integerCoefficient i k • a = integerCoefficient j k • (integerCoefficient i j • a)
    rw [smul_smul, integerCoefficient_comp (leOfHom f) (leOfHom g)]

/-- 概要：乗法列の直極限の標準射は群の cocone。
方針：各段の inclusion を脚に取り、遷移関係を自然性に使う。
規約：cocone の対象は Module.DirectLimit の加法群。
使われ方：HA §1.4.2。直極限と圏論的余極限の比較。 -/
def additiveCocone : Cocone (additiveDiagram A) where
  pt := AddCommGrpCat.of (additiveLimit A)
  ι := {
    app i := AddCommGrpCat.ofHom (inclusion A i).toAddMonoidHom
    naturality i j f := by
      ext a
      exact inclusion_transition A (leOfHom f) a }

/-- 概要：乗法列の直極限は集合の圏でも元の図式の余極限を与える。
方針：代表の全射性と等式の後続段での検出を型の余極限判定へ適用する。
規約：アーベル群からの忘却後の cocone について述べる。
使われ方：HA §1.4.2。乗法列の圏論的余極限性の証明。 -/
def additiveCoconeUnderlyingIsColimit :
    IsColimit ((forget AddCommGrpCat.{u}).mapCocone (additiveCocone A)) := by
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro y
    obtain ⟨i, a, ha⟩ := exists_inclusion A y
    exact ⟨i, a, ha.symm⟩
  · intro i a b h
    obtain ⟨j, hij, hj⟩ := inclusion_eq_eventually A i a b h
    exact ⟨j, homOfLE hij, hj⟩

/-- 概要：乗法列の直極限 cocone はアーベル群の余極限。
方針：集合での余極限性を忘却関手の同型反映で戻す。
規約：元の群 A のねじれを許す。
使われ方：HA §1.4.2。π_* の群の余極限を ℚ テンソルへ同定する。 -/
def additiveCoconeIsColimit : IsColimit (additiveCocone A) := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let : ReflectsColimit (additiveDiagram A) (forget AddCommGrpCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  exact isColimitOfReflects (forget AddCommGrpCat.{u}) (additiveCoconeUnderlyingIsColimit A)

/-- 概要：アーベル群の乗法列の圏論的余極限は A⊗ℚ と同型。
方針：圏論的余極限を直極限へ比較し、実証済みの局所化の線形同型を合成する。
規約：アーベル群の圏の同型。
使われ方：BF 1978 §2、HA §1.4.2。L9d の telescope の群の有理化。 -/
def additiveDiagramTensorIso : colimit (additiveDiagram A) ≅ AddCommGrpCat.of (A ⊗[ℤ] ℚ) :=
  (colimit.isColimit (additiveDiagram A)).coconePointUniqueUpToIso (additiveCoconeIsColimit A) ≪≫
    (additiveLimitTensorEquiv A).toAddEquiv.toAddCommGrpIso

/-- 概要：圏論的な乗法列の有理化は零段の元を a⊗1 へ送る。
方針：二つの余極限の比較と局所化の比較の標準射での計算を使う。
規約：有理化写像の具体的な成分式。
使われ方：HA §1.4.2。スペクトルの有理化写像の π_* の同定。 -/
@[simp]
theorem additiveDiagramTensorIso_zero (a : A) :
    (additiveDiagramTensorIso A).hom.hom ((colimit.ι (additiveDiagram A) 0).hom a) =
      a ⊗ₜ[ℤ] (1 : ℚ) := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (additiveDiagram A)) (additiveCoconeIsColimit A) 0
  have ha := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom h) a
  change (additiveLimitTensorEquiv A)
    (((colimit.isColimit (additiveDiagram A)).coconePointUniqueUpToIso
      (additiveCoconeIsColimit A)).hom.hom ((colimit.ι (additiveDiagram A) 0).hom a)) = _
  rw [show ((colimit.isColimit (additiveDiagram A)).coconePointUniqueUpToIso
      (additiveCoconeIsColimit A)).hom.hom ((colimit.ι (additiveDiagram A) 0).hom a) =
        inclusion A 0 a from ha]
  exact additiveLimitTensorEquiv_zero A a

end

end SerrePositivity.KST.Spectra.RationalTelescope
