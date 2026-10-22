module
public import SerrePositivity.DifferentialGraded.Endomorphism.HomMapNaturality

/-! # 指定 Hom 同型による全パラメータ閉比較の自然性の反映
概要：元の dg 関手の一つの Hom 同型で、閉比較の全 Hom 自然性を反映する。
方針：元の前後合成との可換性を使い、指定した同じ Hom 同型で消去する。
規約：全 Hom 上の式を保持。使われ方：二軸への元の二射の自然性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
private lemma prependSquare {V : Type*} [Category V] {A B C D E : V}
    (f : A ⟶ B) (g : B ⟶ C) (m : C ⟶ E) (n : B ⟶ D) (p : D ⟶ E)
    (h : g ≫ m = n ≫ p) : (f ≫ g) ≫ m = (f ≫ n) ≫ p := by
  simpa only [Category.assoc] using congrArg (fun k => f ≫ k) h

variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]
  {D : Type w} [DGCategory R D]

/-- 元の Hom 同型で、同じ閉比較の全パラメータ自然性を反映できる。 -/
lemma dgClosedComparison_reflect (F : DGFunctor R C D)
    (X X' Y Y' : ClosedCategory R C) {K : Complex R}
    (k : K ⟶ homObject R C X X') (l : K ⟶ homObject R C Y Y')
    (a : X ⟶ Y) (b : X' ⟶ Y')
    (e : homObject R C X Y' ≅ homObject R D (F.obj X) (F.obj Y'))
    (he : e.hom = F.map X Y')
    (h : (k ≫ F.map X X') ≫ eHomWhiskerLeft (Complex R) (F.onClosed.obj X)
        (F.onClosed.map b) =
      (l ≫ F.map Y Y') ≫ eHomWhiskerRight (Complex R) (F.onClosed.map a)
        (F.onClosed.obj Y')) :
    k ≫ eHomWhiskerLeft (Complex R) X b =
      l ≫ eHomWhiskerRight (Complex R) a Y' := by
  apply (cancel_mono e.hom).mp
  rw [he]
  have hl : (k ≫ eHomWhiskerLeft (Complex R) X b) ≫ F.map X Y' =
      (k ≫ F.map X X') ≫ eHomWhiskerLeft (Complex R) (F.onClosed.obj X)
        (F.onClosed.map b) := by
    exact prependSquare k _ _ _ _ (dgHomMap_postcompose F X b)
  have hr : (l ≫ eHomWhiskerRight (Complex R) a Y') ≫ F.map X Y' =
      (l ≫ F.map Y Y') ≫ eHomWhiskerRight (Complex R) (F.onClosed.map a)
        (F.onClosed.obj Y') := by
    exact prependSquare l _ _ _ _ (dgHomMap_precompose F a Y')
  exact hl.trans (h.trans hr.symm)

end SerrePositivity.KST.SConstruction
