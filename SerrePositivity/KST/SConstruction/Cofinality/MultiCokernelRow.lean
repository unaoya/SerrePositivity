module
public import SerrePositivity.KST.SConstruction.Cofinality.CokernelBarIso
public import SerrePositivity.KST.SConstruction.Cofinality.ObstructionDiagramIso

/-!
概要：元の全 S 多次数の K₀ 余核の一方向を元の S 余核へ照合する。
方針：残りの多次数を固定し、先頭方向の元の端点制限を回収する。
規約：反復 S の指定射を同じまま保持する。
使われ方：一方向 bar 同型を元の全多方向障害図式へ接続する。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：残りの全 S 多次数を固定して先頭方向だけを動かす添字関手。
方針：先頭に恒等関手、残りに元の多次数の定値関手を配置する。
規約：外側の S 方向を先頭とする元の順序。
使われ方：元の全多次数図式の一方向の制限。 -/
def completionCokernelHeadIndex (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ) :
    SimplexCategoryᵒᵖ ⥤ (Fin (r + 1) → SimplexCategoryᵒᵖ) :=
  Functor.pi' (fun i => Fin.cases (𝟭 SimplexCategoryᵒᵖ)
    (fun j => (Functor.const SimplexCategoryᵒᵖ).obj (ι j)) i)

/-- 概要：先頭方向の元の構造射は同じ反復 S 模型の元の端点制限。
方針：残りの多次数方向の恒等作用を関手の恒等則で消去する。
規約：完全射の等号であり、別の同値へ置換しない。
使われ方：余核の先頭方向と一方向余核の面・退化の照合。 -/
lemma completionCokernelHead_structureMap (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {d e : SimplexCategoryᵒᵖ} (α : d ⟶ e) (Y : StableModel.{u}) :
    (((multiSEndofunctor (r + 1)).map ((completionCokernelHeadIndex r ι).map α)).app Y) =
      cofinalitySRestriction (((multiSEndofunctor r).obj ι).obj Y) α.unop.toOrderHom := by
  change (sEndofunctor d.unop.len).map (((multiSEndofunctor r).map (𝟙 ι)).app Y) ≫
    (sEndofunctorMap α.unop.toOrderHom).app (((multiSEndofunctor r).obj ι).obj Y) = _
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rfl

/-- 概要：全多次数余核の先頭方向は元の反復 S 射の一方向余核と自然に同型。
方針：各次数の定義的な一致を元の先頭構造射の等号で束ねる。
規約：各多次数で群を選び直さない。
使われ方：元の全多次数障害図式への bar 同型の代入。 -/
def completionCokernelHeadRowIso (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    completionCokernelHeadIndex r ι ⋙ completionKZeroCokernelDiagram (r + 1) f ⋙
        forget AddCommGrpCat.{u} ≅
      cutCokernelSimplicialSet (((multiSEndofunctor r).obj ι).map f) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro d e α
    apply ConcreteCategory.hom_ext
    intro a
    change cutKZeroCokernel d.unop.len (((multiSEndofunctor r).obj ι).map f) at a
    induction a using Quotient.inductionOn with | h a => ?_
    exact congrArg (QuotientAddGroup.mk'
      (triangulatedKZeroSourceMap ((sEndofunctor e.unop.len).map
        (((multiSEndofunctor r).obj ι).map f))).range)
      (DFunLike.congr_fun (congrArg triangulatedKZeroSourceMap
        (completionCokernelHead_structureMap r ι α Y)) a))

/-- 概要：元の全多次数余核の一方向は同じ元の一段余核群の bar と同型。
方針：先頭方向の厳密な比較と元の一方向 bar 同型を合成する。
規約：残りの全 S 多次数は任意に固定できる。
使われ方：全多方向の元の離散的障害の高次消滅。 -/
def completionCokernelHeadBarIso (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    completionCokernelHeadIndex r ι ⋙ completionKZeroCokernelDiagram (r + 1) f ⋙
        forget AddCommGrpCat.{u} ≅
      nerve (AsSmall.{u} (SingleObj (Multiplicative
        (cutKZeroCokernel 1 (((multiSEndofunctor r).obj ι).map f))))) :=
  completionCokernelHeadRowIso r ι f ≪≫ cutCokernelBarIso (((multiSEndofunctor r).obj ι).map f)

end SerrePositivity.KST.SConstruction.Cofinality
