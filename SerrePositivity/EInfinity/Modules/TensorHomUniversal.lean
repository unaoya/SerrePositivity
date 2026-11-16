module

public import SerrePositivity.EInfinity.Modules.TensorDoldKanBifunctor

/-!
# 同じ加群テンソル frame の恒等射による全普遍 Hom 族

概要：M10 の同じ実 frame 射を、元の dg Hom の全代表可能族へ送る。
方針：同じ Yoneda 同値と検証済みの二変数 Dold–Kan 同型を合成する。
規約：HA 1.3.1.13、全次数・全標的射・全作用素を保持する。
使われ方：全評価屋根と元の dg 係数の全高次評価の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory Opposite SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：元の frame 射を同じ全 Hom の代表可能族にする。
方針：同じ単体自身に Yoneda 同値の逆を適用する。
規約：HA 1.3.1.13、元の射。使われ方：普遍評価の全パラメータ。 -/
def moduleTensorHomRepresentable (P N : ModuleCategory A D) (n : SimplexCategory)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) :
    stdSimplex.obj n ⟶ (cosimplicialHom ((moduleTensorSimplicesFunctor A D).obj P)).obj N :=
  SSet.yonedaEquiv.symm g

/-- 概要：同じ代表可能族は元の全標的射と可換。
方針：同じ Yoneda 同値で全単体を照合する。
規約：HA 1.3.1.13、同じ後合成。使われ方：全評価の回収。 -/
lemma moduleTensorHomRepresentable_postcomp (P : ModuleCategory A D)
    {N N' : ModuleCategory A D} (n : SimplexCategory)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) (h : N ⟶ N') :
    moduleTensorHomRepresentable A D P N n g ≫
      (cosimplicialHom ((moduleTensorSimplicesFunctor A D).obj P)).map h =
        moduleTensorHomRepresentable A D P N' n (g ≫ h) := by
  apply SSet.yonedaEquiv.injective
  simp only [moduleTensorHomRepresentable, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

/-- 概要：同じ代表可能族は元の全単体作用素と可換。
方針：Yoneda 同値の同じ始域自然性を使う。
規約：HA 1.3.1.13、同じ前合成。使われ方：全次数の貼り合わせ。 -/
lemma moduleTensorHomRepresentable_reindex (P N : ModuleCategory A D)
    {n m : SimplexCategory} (f : n ⟶ m)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj m ⟶ N) :
    stdSimplex.map f ≫ moduleTensorHomRepresentable A D P N m g =
      moduleTensorHomRepresentable A D P N n
        (((moduleTensorSimplicesFunctor A D).obj P).map f ≫ g) :=
  SSet.yonedaEquiv_symm_naturality_left
    (X := (cosimplicialHom ((moduleTensorSimplicesFunctor A D).obj P)).obj N) f g

/-- 概要：同じ元の frame 射の全族を元の dg Hom の実 Dold–Kan に送る。
方針：同じ代表可能族の後に同じ全単体同型を合成する。
規約：HA 1.3.1.13、元の主 Hom end。使われ方：dg 係数の実全評価。 -/
def moduleTensorHomDoldKanSimplex (P N : ModuleCategory A D) (n : SimplexCategory)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) :
    stdSimplex.obj n ⟶ ((moduleDoldKanHomBifunctor A D).obj (op P)).obj N :=
  moduleTensorHomRepresentable A D P N n g ≫ (((moduleTensorHomDoldKanBifunctorIso A D).app (op P)).app N).hom

/-- 概要：同じ dg Hom 族は全標的射の元の作用と可換。
方針：同じ全標的自然同型と代表可能族の後合成則を使う。
規約：HA 1.3.1.13、同じ作用。使われ方：全評価の回収。 -/
lemma moduleTensorHomDoldKanSimplex_postcomp (P : ModuleCategory A D)
    {N N' : ModuleCategory A D} (n : SimplexCategory)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) (h : N ⟶ N') :
    moduleTensorHomDoldKanSimplex A D P N n g ≫
      ((moduleDoldKanHomBifunctor A D).obj (op P)).map h =
        moduleTensorHomDoldKanSimplex A D P N' n (g ≫ h) := by
  dsimp only [moduleTensorHomDoldKanSimplex]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => moduleTensorHomRepresentable A D P N n g ≫ k)
      (((moduleTensorHomDoldKanBifunctorIso A D).app (op P)).hom.naturality h).symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫
          (((moduleTensorHomDoldKanBifunctorIso A D).app (op P)).app N').hom)
          (moduleTensorHomRepresentable_postcomp A D P n g h))))

/-- 概要：同じ dg Hom 族は全単体作用素と可換。
方針：元の代表可能族の始域自然性を同じ同型で送る。
規約：HA 1.3.1.13、全作用素。使われ方：全高次係数の貼り合わせ。 -/
lemma moduleTensorHomDoldKanSimplex_reindex (P N : ModuleCategory A D)
    {n m : SimplexCategory} (f : n ⟶ m)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj m ⟶ N) :
    stdSimplex.map f ≫ moduleTensorHomDoldKanSimplex A D P N m g =
      moduleTensorHomDoldKanSimplex A D P N n
        (((moduleTensorSimplicesFunctor A D).obj P).map f ≫ g) := by
  dsimp only [moduleTensorHomDoldKanSimplex]
  rw [← Category.assoc, moduleTensorHomRepresentable_reindex]

/-- 概要：同じ実 frame の恒等射が与える元の dg Hom の普遍族。
方針：同じ全族に元の恒等射を代入する。
規約：HA 1.3.1.13、同じ単体係数。使われ方：全 cone の元の普遍成分。 -/
def moduleTensorUniversalDoldKanSimplex (P : ModuleCategory A D) (n : SimplexCategory) :
    stdSimplex.obj n ⟶ ((moduleDoldKanHomBifunctor A D).obj (op P)).obj
      (((moduleTensorSimplicesFunctor A D).obj P).obj n) :=
  moduleTensorHomDoldKanSimplex A D P _ n (𝟙 _)

/-- 概要：同じ普遍族の評価は元の frame 射の全族そのもの。
方針：同じ後合成則と恒等射の法則を使う。
規約：HA 1.3.1.13、同じ射。使われ方：全評価三角形。 -/
lemma moduleTensorUniversalDoldKanSimplex_evaluation (P N : ModuleCategory A D)
    (n : SimplexCategory) (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) :
    moduleTensorUniversalDoldKanSimplex A D P n ≫
      ((moduleDoldKanHomBifunctor A D).obj (op P)).map g =
        moduleTensorHomDoldKanSimplex A D P N n g := by
  simpa only [moduleTensorUniversalDoldKanSimplex, Category.id_comp] using
    moduleTensorHomDoldKanSimplex_postcomp A D P n (𝟙 _) g

/-- 概要：同じ普遍族は元の frame 全作用素と可換。
方針：同じ評価式と元の始域自然性を貼り合わせる。
規約：HA 1.3.1.13、同じ全次数。使われ方：全係数 cone の自然性。 -/
lemma moduleTensorUniversalDoldKanSimplex_naturality (P : ModuleCategory A D)
    {n m : SimplexCategory} (f : n ⟶ m) :
    stdSimplex.map f ≫ moduleTensorUniversalDoldKanSimplex A D P m =
      moduleTensorUniversalDoldKanSimplex A D P n ≫
        ((moduleDoldKanHomBifunctor A D).obj (op P)).map
          (((moduleTensorSimplicesFunctor A D).obj P).map f) := by
  rw [moduleTensorUniversalDoldKanSimplex_evaluation]
  simpa only [moduleTensorUniversalDoldKanSimplex, Category.comp_id] using
    moduleTensorHomDoldKanSimplex_reindex A D P
      (((moduleTensorSimplicesFunctor A D).obj P).obj m) f (𝟙 _)

end SerrePositivity.EInfinity.Modules
