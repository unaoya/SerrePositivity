module
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientProductComponents

/-! # 同じ全図式移送の四成分と元の BF 表示・両射影同値
概要：四成分を、元の BF 表示の同型と元の Tamme 射影同値そのものへ照合する。
方針：端点の等号による移送を、Arrow の等号として除く。
規約：同じ元の図式の比較を保持する。使われ方：移送後の四辺の射の類の計算。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
namespace PerfectLaxQuotient
variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B}
  (d : PerfectLaxQuotient p q)
  {F : perfectStableInfinity.{u} ⟶ Sp.{u}} (hF : IsPerfectLocalizingInvariant F)

/-- 左下の成分は、元の左端の同じ BF 表示への比較。 -/
lemma productComponent00_arrow : Arrow.mk (d.productComponent hF 0 0) =
    Arrow.mk (perfectInvariantSpectrumIso F (perfectStableVertex d.left d.left_complete)).inv := by
  rw [d.productComponent_arrow]
  change Arrow.mk (eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj Sp.{u}))
    (d.universalValueSquare_vertex00 F)) ≫
      (perfectInvariantSpectrumIso F (perfectStableVertex d.left d.left_complete)).inv) = _
  exact arrow_mk_eqToHom_comp _ _

/-- 左上の成分は、元の完備化先の同じ BF 表示への比較。 -/
lemma productComponent01_arrow : Arrow.mk (d.productComponent hF 0 1) =
    Arrow.mk (perfectInvariantSpectrumIso F d.sequence.rightVertex).inv := by
  rw [d.productComponent_arrow]
  change Arrow.mk (eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj Sp.{u}))
    (d.universalValueSquare_vertex01 F)) ≫
      (perfectInvariantSpectrumIso F d.sequence.rightVertex).inv) = _
  exact arrow_mk_eqToHom_comp _ _

/-- 右下の成分は、同じ BF 表示から元の両射影を持つ Tamme 同値への合成。 -/
lemma productComponent10_arrow : Arrow.mk (d.productComponent hF 1 0) =
    Arrow.mk ((perfectInvariantSpectrumIso F
      (perfectLaxVertex p q d.c_complete d.d_complete)).inv ≫
        (hF.tammePerfectProjectionEquivalence p q d.c_complete d.d_complete).hom) := by
  rw [d.productComponent_arrow]
  change Arrow.mk (eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj Sp.{u}))
    (d.universalValueSquare_vertex10 F)) ≫
      ((perfectInvariantSpectrumIso F (perfectLaxVertex p q d.c_complete d.d_complete)).inv ≫
        (hF.tammePerfectProjectionEquivalence p q d.c_complete d.d_complete).hom)) = _
  exact arrow_mk_eqToHom_comp _ _

/-- 右上の成分は、同じ BF 表示から恒等 lax 圏の元の両射影同値への合成。 -/
lemma productComponent11_arrow : Arrow.mk (d.productComponent hF 1 1) =
    Arrow.mk ((perfectInvariantSpectrumIso F
      (perfectLaxVertex (𝟙 d.sequence.right) (𝟙 d.sequence.right)
        d.sequence.right_complete d.sequence.right_complete)).inv ≫
          (hF.tammePerfectProjectionEquivalence (𝟙 d.sequence.right) (𝟙 d.sequence.right)
            d.sequence.right_complete d.sequence.right_complete).hom) := by
  rw [d.productComponent_arrow]
  change Arrow.mk (eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj Sp.{u}))
    (d.universalValueSquare_vertex11 F)) ≫
      ((perfectInvariantSpectrumIso F
        (perfectLaxVertex (𝟙 d.sequence.right) (𝟙 d.sequence.right)
          d.sequence.right_complete d.sequence.right_complete)).inv ≫
            (hF.tammePerfectProjectionEquivalence (𝟙 d.sequence.right) (𝟙 d.sequence.right)
              d.sequence.right_complete d.sequence.right_complete).hom)) = _
  exact arrow_mk_eqToHom_comp _ _

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
