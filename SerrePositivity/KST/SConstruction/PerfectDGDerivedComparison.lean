module
public import SerrePositivity.KST.SConstruction.ProjectiveGraphComparison

/-! # 実 Perf dg 延長と主導来延長の H⁰ 自然比較
概要：全次数の実 dg 関手の H⁰ と、主導来延長を同じ Perf 入力上で比較する。
方針：閉零射上の射影的比較を、境界商の射の全射性で H⁰ の全射へ延長する。
規約：比較は元の graph 延長を保持する。使われ方：Morita の全次数 Hom 判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded

private lemma threeComparisonSquares {C : Type*} [Category* C]
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : C}
    (f₀ : a₀ ⟶ b₀) (f₁ : a₁ ⟶ b₁) (f₂ : a₂ ⟶ b₂) (f₃ : a₃ ⟶ b₃)
    (a : a₀ ⟶ a₁) (b : a₁ ⟶ a₂) (c : a₂ ⟶ a₃)
    (d : b₀ ⟶ b₁) (e : b₁ ⟶ b₂) (f : b₂ ⟶ b₃)
    (h₀ : f₀ ≫ d = a ≫ f₁) (h₁ : f₁ ≫ e = b ≫ f₂)
    (h₂ : f₂ ≫ f = c ≫ f₃) : f₀ ≫ (d ≫ e ≫ f) = (a ≫ b ≫ c) ≫ f₃ := by
  simp only [Category.assoc]
  rw [← Category.assoc f₀, h₀, Category.assoc, ← Category.assoc f₁, h₁,
    Category.assoc, h₂]

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- H⁰ の各元の対象上で、実 Perf dg 延長と主導来延長を照合する。 -/
def perfectDGDerivedComparisonAt (X : PerfectDGHomotopyCategoryOver A D Set.univ) :
    (dgDerivedExtension A D E F).obj ((perfectDGModuleToDerived A D Set.univ).obj X) ≅
      (perfectDGModuleToDerived A E Set.univ).obj ((perfectDGExtension A D E F).onHomotopy.obj X) :=
  (dgDerivedExtension A D E F).mapIso
      ((perfectDGModuleClosedToDerivedIso A D Set.univ).app X.as) ≪≫
    projectiveGraphComparison A D E F
      ((perfectDGModuleInclusion A D Set.univ).onClosed.obj X.as)
      (ForgetEnrichment.to (Complex A) X.as).property.1 ≪≫
    ((perfectDGModuleClosedToDerivedIso A E Set.univ).app
      ((perfectDGExtension A D E F).onClosed.obj X.as)).symm

/-- 主導来延長との比較は、H⁰ の全射について自然。 -/
lemma perfectDGDerivedComparisonAt_naturality
    {X Y : PerfectDGHomotopyCategoryOver A D Set.univ} (f : X ⟶ Y) :
    (dgDerivedExtension A D E F).map ((perfectDGModuleToDerived A D Set.univ).map f) ≫
        (perfectDGDerivedComparisonAt A D E F Y).hom =
      (perfectDGDerivedComparisonAt A D E F X).hom ≫
        (perfectDGModuleToDerived A E Set.univ).map
          ((perfectDGExtension A D E F).onHomotopy.map f) := by
  obtain ⟨f, rfl⟩ := (toHomotopy A (PerfectDGModule A D)).map_surjective f
  dsimp only [perfectDGDerivedComparisonAt, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  apply threeComparisonSquares
  · exact (Functor.map_comp _ _ _).symm.trans
      ((congrArg (dgDerivedExtension A D E F).map
        ((perfectDGModuleClosedToDerivedIso A D Set.univ).hom.naturality f)).trans
        (Functor.map_comp _ _ _))
  · exact projectiveGraphComparison_naturality A D E F _ _
      ((perfectDGModuleInclusion A D Set.univ).onClosed.map f)
  · exact (perfectDGModuleClosedToDerivedIso A E Set.univ).inv.naturality
      ((perfectDGExtension A D E F).onClosed.map f)

/-- 実 Perf dg 関手の H⁰ と主導来延長の実自然同型。 -/
def perfectDGDerivedComparison :
    perfectDGModuleToDerived A D Set.univ ⋙ dgDerivedExtension A D E F ≅
      (perfectDGExtension A D E F).onHomotopy ⋙ perfectDGModuleToDerived A E Set.univ :=
  NatIso.ofComponents (perfectDGDerivedComparisonAt A D E F)
    (fun f => perfectDGDerivedComparisonAt_naturality A D E F f)

end SerrePositivity.KST.SConstruction
