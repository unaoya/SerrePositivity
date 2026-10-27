module

public import SerrePositivity.KST.Spectra.D3ParameterComparisonStage

/-!
概要：元のパラメータ制限の関手同型が合成・恒等・逆射を保持することを認証する。
方針：同じ豊穣変換の因子分解を全関手空間の指定順射の合成へ送る。
規約：逆向きの表示を選び直さず、構成済み同型の指定値そのものを比較する。
使われ方：共同単位比較の段制限を、以前の逆単位による実面比較へ厳密に接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 同じパラメータ同型の制限は、全関手空間で元の逆向きの合成を保持する。 -/
lemma d3PointedKanPreFunctorIso_comp {A B C : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (j : C ⟶ A) [IsIso i] [IsIso j] :
    d3PointedKanPreFunctorIso i ≪≫ d3PointedKanPreFunctorIso j =
      d3PointedKanPreFunctorIso (j ≫ i) := by
  apply Iso.ext
  change d3GradedHom (d3PointedKanPre i) ≫ d3GradedHom (d3PointedKanPre j) =
    d3GradedHom (d3PointedKanPre (j ≫ i))
  rw [d3GradedHom_comp]
  have h : d3GradedComp (d3PointedKanPre i) (d3PointedKanPre j) =
      d3PointedKanPre (j ≫ i) := by
    apply GradedNatTrans.ext
    funext X
    exact (d3PointedKanPre_factorization i j X).symm
  rw [h]

/-- 元の恒等パラメータから構成した同型は、関手空間の恒等同型そのもの。 -/
lemma d3PointedKanPreFunctorIso_id (A : PointedSimplicialSet.{u}) :
    d3PointedKanPreFunctorIso (𝟙 A) = Iso.refl _ := by
  have h := congrArg Iso.hom (d3PointedKanPreFunctorIso_comp (𝟙 A) (𝟙 A))
  simp only [Category.id_comp, Iso.trans_hom] at h
  apply Iso.ext
  apply (cancel_epi (d3PointedKanPreFunctorIso (𝟙 A)).hom).1
  simpa only [Iso.refl_hom, Category.comp_id] using h

/-- 元の逆パラメータ同型による比較は、元の順方向比較の逆そのもの。 -/
lemma d3PointedKanPreFunctorIso_inv {A B : PointedSimplicialSet.{u}} (e : A ≅ B) :
    d3PointedKanPreFunctorIso e.inv = (d3PointedKanPreFunctorIso e.hom).symm := by
  apply Iso.ext
  apply (cancel_epi (d3PointedKanPreFunctorIso e.hom).hom).1
  have h := congrArg Iso.hom (d3PointedKanPreFunctorIso_comp e.hom e.inv)
  simp only [Iso.inv_hom_id, d3PointedKanPreFunctorIso_id] at h
  simpa only [Iso.trans_hom, Iso.refl_hom, Iso.symm_hom, Iso.hom_inv_id] using h

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
