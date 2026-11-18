module

public import SerrePositivity.EInfinity.Modules.TensorHomUniversal
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DoldKanPinchedChainNaturality

/-!
# 同じ全加群の普遍評価族と元の dg nerve の pinched Hom

概要：M10 の全普遍 dg Hom 族を元の全通常 dg 加群の pinched Hom へ送る。
方針：同じ実 Dold–Kan/pinched 同型と任意 Hom 鎖写像への自然性を使う。
規約：HA 1.3.1.13、Kerodon 2.5.9（Tag 00SC）、係数加群の半自由性を要求しない。
使われ方：元の全係数 cone の線形成分と全評価屋根の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory Opposite SSet
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories
open DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：元の主 Hom end の実 Γ は全通常加群 dg nerve の同じ pinched Hom。
方針：既存の同じ実 Dold–Kan 同型を元の二対象に適用する。
規約：HA 1.3.1.13、全単体。使われ方：元の普遍族の指定座標。 -/
def moduleDoldKanPinchedIso (P N : ModuleCategory A D) :
    SSet.uliftFunctor.{max (u + 1) v, u}.obj
      (((moduleDoldKanHomBifunctor A D).obj (op P)).obj N) ≅
    PinchedHom.pinchedHom A (RightModule A D)
      (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) N) :=
  doldKanHomPinchedIso (R := A) (D := RightModule A D)
    (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) N)

/-- 概要：同じ座標同型は元の全標的射の作用と可換。
方針：既存の任意 Hom 鎖写像への自然性を同じ後合成に適用する。
規約：HA 1.3.1.13、同じ作用。使われ方：実評価と係数移送。 -/
lemma moduleDoldKanPinchedIso_postcomp (P : ModuleCategory A D)
    {N N' : ModuleCategory A D} (h : N ⟶ N') :
    SSet.uliftFunctor.{max (u + 1) v, u}.map
      (((moduleDoldKanHomBifunctor A D).obj (op P)).map h) ≫
        (moduleDoldKanPinchedIso A D P N').hom =
    (moduleDoldKanPinchedIso A D P N).hom ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) P h) :=
  _root_.SerrePositivity.ComplexLimits.doldKanHomPinchedIso_chainMap (D := RightModule A D) (E := RightModule A D)
    (x := ForgetEnrichment.to (Complex A) P) (y := ForgetEnrichment.to (Complex A) N)
    (x' := ForgetEnrichment.to (Complex A) P) (y' := ForgetEnrichment.to (Complex A) N')
    (eHomWhiskerLeft (Complex A) P h)

/-- 概要：元の実 frame 射の全族を同じ pinched Hom へ送る。
方針：同じ実 Γ 族を持ち上げ、同じ座標同型を後合成する。
規約：HA 1.3.1.13、元の射。使われ方：全係数 cone の実評価。 -/
def moduleTensorHomPinchedSimplex (P N : ModuleCategory A D) (n : SimplexCategory)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) :
    SSet.uliftFunctor.{max (u + 1) v, u}.obj (SSet.stdSimplex.obj n) ⟶
    PinchedHom.pinchedHom A (RightModule A D)
      (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) N) :=
  SSet.uliftFunctor.{max (u + 1) v, u}.map (moduleTensorHomDoldKanSimplex A D P N n g) ≫
    (moduleDoldKanPinchedIso A D P N).hom

/-- 概要：同じ全 pinched 族は元の全標的射と可換。
方針：同じ座標の自然性と元の全 Γ 族の後合成則を合成する。
規約：HA 1.3.1.13、同じ射。使われ方：全評価の回収。 -/
lemma moduleTensorHomPinchedSimplex_postcomp (P : ModuleCategory A D)
    {N N' : ModuleCategory A D} (n : SimplexCategory)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) (h : N ⟶ N') :
    moduleTensorHomPinchedSimplex A D P N n g ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) P h) =
        moduleTensorHomPinchedSimplex A D P N' n (g ≫ h) := by
  dsimp only [moduleTensorHomPinchedSimplex]
  rw [Category.assoc, ← moduleDoldKanPinchedIso_postcomp,
    ← Category.assoc, ← SSet.uliftFunctor.map_comp, moduleTensorHomDoldKanSimplex_postcomp]

/-- 概要：同じ全 pinched 族は元の全単体作用素と可換。
方針：元の全 Γ 族の再添字式を同じ持ち上げと座標で送る。
規約：HA 1.3.1.13、全作用素。使われ方：全係数の貼り合わせ。 -/
lemma moduleTensorHomPinchedSimplex_reindex (P N : ModuleCategory A D)
    {n m : SimplexCategory} (f : n ⟶ m)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj m ⟶ N) :
    SSet.uliftFunctor.{max (u + 1) v, u}.map (SSet.stdSimplex.map f) ≫
      moduleTensorHomPinchedSimplex A D P N m g =
    moduleTensorHomPinchedSimplex A D P N n
      (((moduleTensorSimplicesFunctor A D).obj P).map f ≫ g) := by
  dsimp only [moduleTensorHomPinchedSimplex]
  rw [← Category.assoc, ← SSet.uliftFunctor.map_comp, moduleTensorHomDoldKanSimplex_reindex]

/-- 概要：元のテンソル frame の恒等射による同じ普遍 pinched 族。
方針：同じ実全族に元の恒等射を代入する。
規約：HA 1.3.1.13、元の係数。使われ方：全 cone の普遍成分。 -/
def moduleTensorUniversalPinchedSimplex (P : ModuleCategory A D) (n : SimplexCategory) :
    SSet.uliftFunctor.{max (u + 1) v, u}.obj (SSet.stdSimplex.obj n) ⟶
    PinchedHom.pinchedHom A (RightModule A D) (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) (((moduleTensorSimplicesFunctor A D).obj P).obj n)) :=
  moduleTensorHomPinchedSimplex A D P _ n (𝟙 _)

/-- 概要：同じ普遍 pinched 族の評価は元の実 frame 射の全族。
方針：同じ全後合成則と恒等射の法則を使う。
規約：HA 1.3.1.13、同じ評価。使われ方：全評価三角形。 -/
lemma moduleTensorUniversalPinchedSimplex_evaluation (P N : ModuleCategory A D)
    (n : SimplexCategory) (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) :
    moduleTensorUniversalPinchedSimplex A D P n ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) P g) =
        moduleTensorHomPinchedSimplex A D P N n g := by
  simpa only [moduleTensorUniversalPinchedSimplex, Category.id_comp] using
    moduleTensorHomPinchedSimplex_postcomp A D P n (𝟙 _) g

/-- 概要：同じ普遍 pinched 族は元の frame 全作用素と可換。
方針：同じ全評価式と元の再添字式を貼り合わせる。
規約：HA 1.3.1.13、全作用素。使われ方：全 cone の係数自然性。 -/
lemma moduleTensorUniversalPinchedSimplex_naturality (P : ModuleCategory A D)
    {n m : SimplexCategory} (f : n ⟶ m) :
    SSet.uliftFunctor.{max (u + 1) v, u}.map (SSet.stdSimplex.map f) ≫
      moduleTensorUniversalPinchedSimplex A D P m =
    moduleTensorUniversalPinchedSimplex A D P n ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) P
        (((moduleTensorSimplicesFunctor A D).obj P).map f)) := by
  rw [moduleTensorUniversalPinchedSimplex_evaluation]
  simpa only [moduleTensorUniversalPinchedSimplex, Category.comp_id] using
    moduleTensorHomPinchedSimplex_reindex A D P
      (((moduleTensorSimplicesFunctor A D).obj P).obj m) f (𝟙 _)

end SerrePositivity.EInfinity.Modules
