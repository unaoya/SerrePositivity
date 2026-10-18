module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
概要：複体の図式を関手圏内の複体として組み直し、余極限の項別計算を比較する。
方針：次数と図式の添字を入れ替え、評価の余極限保存の同型を微分と両立させる。
規約：任意の複体形状。
使われ方：Stacks Lemma 19.12.4・Theorem 19.12.6、TT §3・§8、Toën §3.2 の非有界分解の余極限。
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
概要：複体の図式を関手圏内の複体へ転置する。
方針：各次数は評価との合成、微分は元の各複体の微分を成分に持つ自然変換。
規約：微分の可換性は元の鎖写像の条件。
使われ方：Stacks Theorem 19.12.6、TT §3 の余極限の完全性。
-/
def complexDiagramTranspose (F : J ⥤ HomologicalComplex C c) : HomologicalComplex (J ⥤ C) c where
  X i := F ⋙ HomologicalComplex.eval C c i
  d i j :=
    { app k := (F.obj k).d i j
      naturality k k' f := (F.map f).comm i j }
  shape i j hij := by ext k; exact (F.obj k).shape i j hij
  d_comp_d' i j k _ _ := by ext a; exact (F.obj a).d_comp_d i j k

/--
概要：複体の余極限は転置した関手圏内の複体への項別余極限と同型。
方針：各次数の評価の余極限比較を鎖写像の可換性でつなぐ。
規約：余極限の完全性はこの同型自体には不要。
使われ方：Stacks Lemma 19.12.4・Theorem 19.12.6、TT §3 の非輪状性の余極限保存。
-/
def colimitComplexTransposeIso [HasColimitsOfShape J C]
    (F : J ⥤ HomologicalComplex C c) :
    colimit F ≅ ((colim : (J ⥤ C) ⥤ C).mapHomologicalComplex c).obj (complexDiagramTranspose c F) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => preservesColimitIso (HomologicalComplex.eval C c i) F)
    (by
      intro i j hij
      apply (cancel_epi (preservesColimitIso (HomologicalComplex.eval C c i) F).inv).mp
      apply colimit.hom_ext
      intro k
      simp only [Category.assoc, Iso.inv_hom_id_assoc, ι_preservesColimitIso_inv_assoc]
      change colimit.ι (F ⋙ HomologicalComplex.eval C c i) k ≫
          colim.map ((complexDiagramTranspose c F).d i j) =
        (colimit.ι F k).f i ≫ (colimit F).d i j ≫
          (preservesColimitIso (HomologicalComplex.eval C c j) F).hom
      rw [← Category.assoc, (colimit.ι F k).comm, Category.assoc]
      simp [complexDiagramTranspose]
      exact congrArg (fun f => (F.obj k).d i j ≫ f)
        (ι_preservesColimitIso_hom (HomologicalComplex.eval C c j) F k).symm)

end SerrePositivity.KST.DerivedGeometry
