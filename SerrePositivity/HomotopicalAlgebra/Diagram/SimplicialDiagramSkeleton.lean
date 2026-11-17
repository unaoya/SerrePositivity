module
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-!
概要：単体集合値図式の骨格を元の評価先の全射で自然な図式として組み立てる。
方針：各単体集合の同じ骨格に射を制限し、自然な骨格の塔と元の図式への余錐を取る。
規約：IS-W2 R03aの境界細胞の証明分割。元の図式の単体を変更しない。
使われ方：自由境界の段階的な付着と全体への余極限。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
open CategoryTheory Limits SSet
open scoped Simplicial

/-- 元の単体写像は同じ次数の骨格を保つ。 -/
theorem skeleton_image_le {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    (X.skeleton n).image f ≤ Y.skeleton n := by
  rw [Subcomplex.image_le_iff]
  change (⨆ (k : Fin n) (x : X.nonDegenerate k), Subcomplex.ofSimplex x.val) ≤ _
  refine iSup_le (fun k => iSup_le (fun x => ?_))
  rw [Subcomplex.ofSimplex_le_iff]
  change f.app _ x.val ∈ (Y.skeleton n).obj _
  exact Y.mem_skeleton _ k.isLt

/-- 元の写像の同じ骨格への制限。 -/
def skeletonMap {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    (X.skeleton n : SSet.{u}) ⟶ (Y.skeleton n : SSet.{u}) :=
  Subcomplex.lift ((X.skeleton n).ι ≫ f) (by
    rw [← Subcomplex.image_eq_range]
    exact skeleton_image_le f n)

/-- 骨格への制限後の包含は、元の同じ写像。 -/
@[reassoc] theorem skeletonMap_ι {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    skeletonMap f n ≫ (Y.skeleton n).ι = (X.skeleton n).ι ≫ f := rfl

/-- 骨格への制限は同じ恒等写像を保つ。 -/
theorem skeletonMap_id (X : SSet.{u}) (n : ℕ) : skeletonMap (𝟙 X) n = 𝟙 _ := by
  apply (cancel_mono (X.skeleton n).ι).mp
  rw [skeletonMap_ι, Category.comp_id, Category.id_comp]

/-- 骨格への制限は元の写像の合成を保つ。 -/
theorem skeletonMap_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    skeletonMap (f ≫ g) n = skeletonMap f n ≫ skeletonMap g n := by
  apply (cancel_mono (Z.skeleton n).ι).mp
  simp only [Category.assoc, skeletonMap_ι, skeletonMap_ι_assoc]

variable (I : Type u) [SmallCategory I] (W : I ⥤ SSet.{u})

/-- 元の図式の各値の同じ骨格を集めた全族。 -/
def skeletonFamily : I ⥤ ℕ ⥤ SSet.{u} where
  obj i := (W.obj i).skeleton.monotone.functor ⋙ Subcomplex.toSSetFunctor
  map f :=
    { app n := skeletonMap (W.map f) n
      naturality n m h := by
        apply SSet.hom_ext
        intro d
        apply ConcreteCategory.hom_ext
        intro x
        apply Subtype.ext
        rfl }
  map_id i := by
    apply NatTrans.ext
    funext n
    change skeletonMap (W.map (𝟙 i)) n = 𝟙 _
    rw [CategoryTheory.Functor.map_id, skeletonMap_id]
  map_comp f g := by
    apply NatTrans.ext
    funext n
    change skeletonMap (W.map (f ≫ g)) n =
      skeletonMap (W.map f) n ≫
        skeletonMap (W.map g) n
    rw [CategoryTheory.Functor.map_comp, skeletonMap_comp]

/-- 同じ単体集合値図式の骨格の塔。 -/
def skeletonFiltration : ℕ ⥤ I ⥤ SSet.{u} := (skeletonFamily I W).flip

/-- 同じ骨格の塔から元の図式重みへの余錐。 -/
def skeletonCocone : Cocone (skeletonFiltration I W) where
  pt := W
  ι :=
    { app n :=
        { app i := ((W.obj i).skeleton n).ι
          naturality i j f := skeletonMap_ι (W.map f) n }
      naturality n m h := by
        apply NatTrans.ext
        funext i
        rfl }

/-- 同じ全骨格の余極限は、元の図式重みそのもの。 -/
def skeletonCoconeIsColimit : IsColimit (skeletonCocone I W) := by
  apply evaluationJointlyReflectsColimits _
  intro i
  let X := W.obj i
  exact IsColimit.ofIsoColimit
    (isColimitOfPreserves Subcomplex.toSSetFunctor
      ((CompleteLattice.colimitCocone X.skeleton.monotone.functor).isColimit))
    (Cocone.ext (Subcomplex.eqToIso (X.iSup_skeleton) ≪≫ Subcomplex.topIso X))

end SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
