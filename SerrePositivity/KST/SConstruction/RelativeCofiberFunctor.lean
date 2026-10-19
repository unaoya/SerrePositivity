module
public import SerrePositivity.KST.SConstruction.RelativeStableModels
public import SerrePositivity.KST.SConstruction.CofiberEndofunctor

/-! # 相対 E(A,C,B) の関手性
概要：両端の閉じた条件を保つ完全関手が相対 cofiber 図式の完全関手を誘導する。
方針：元の cofiber 後合成の評価の自然性で所属条件を保ち、全部分圏に制限する。
規約：全 cofiber の選択を保持する。使われ方：相対加法性の入力自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 両端の条件を保つ完全関手の後合成は相対 cofiber 条件を保つ。 -/
lemma relativeCofiberPostcomp_mem {X Y : RelativeStableModel.{u}} (f : X ⟶ Y)
    (v : (cofiberDiagrams X.ambient.carrier) _⦋0⦌)
    (hv : (relativeCofiberPredicate X.left X.right).predicate v) :
    (relativeCofiberPredicate Y.left Y.right).predicate
      ((cofiberEndofunctor.map f.val).val.app (Opposite.op ⦋0⦌) v) := by
  have hs := congrArg
    (fun g : cofiberStableModel X.ambient ⟶ Y.ambient => g.val.app (Opposite.op ⦋0⦌) v)
    (cofiberSubobjectNat.naturality f.val)
  have hq := congrArg
    (fun g : cofiberStableModel X.ambient ⟶ Y.ambient => g.val.app (Opposite.op ⦋0⦌) v)
    (cofiberQuotientNat.naturality f.val)
  exact ⟨(congrArg Y.left.predicate hs).mpr (f.property.1 _ hv.1),
    (congrArg Y.right.predicate hq).mpr (f.property.2 _ hv.2)⟩

/-- 相対入力の完全関手から誘導される相対 cofiber 図式の完全関手。 -/
def relativeCofiberMap {X Y : RelativeStableModel.{u}} (f : X ⟶ Y) :
    relativeCofiberStableModel X.left X.right ⟶ relativeCofiberStableModel Y.left Y.right :=
  closedStableMap (relativeCofiberPredicate X.left X.right)
    (relativeCofiberPredicate Y.left Y.right) (cofiberEndofunctor.map f.val)
    (fun v hv => relativeCofiberPostcomp_mem f v hv)

/-- 相対図式の完全関手は包含後に元の全 cofiber 後合成を回収する。 -/
lemma relativeCofiberMap_inclusion {X Y : RelativeStableModel.{u}} (f : X ⟶ Y) :
    relativeCofiberMap f ≫ relativeCofiberInclusion Y.left Y.right =
      relativeCofiberInclusion X.left X.right ≫ cofiberEndofunctor.map f.val :=
  closedStableMap_inclusion _ _ _ _

/-- 相対 E(A,C,B) を安定な入力の完全関手として関手化する。 -/
def relativeCofiberFunctor : RelativeStableModel.{u} ⥤ StableModel.{u} where
  obj X := relativeCofiberStableModel X.left X.right
  map f := relativeCofiberMap f
  map_id X := by
    apply closedStableInclusion_cancel (relativeCofiberPredicate X.left X.right)
    change relativeCofiberMap (𝟙 X) ≫ relativeCofiberInclusion X.left X.right = _
    rw [relativeCofiberMap_inclusion]
    change relativeCofiberInclusion X.left X.right ≫ cofiberEndofunctor.map (𝟙 X.ambient) = _
    exact (congrArg (fun t => relativeCofiberInclusion X.left X.right ≫ t)
      (cofiberEndofunctor.map_id X.ambient)).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)
  map_comp {X Y Z} f g := by
    apply closedStableInclusion_cancel (relativeCofiberPredicate Z.left Z.right)
    calc
      _ = relativeCofiberInclusion X.left X.right ≫ cofiberEndofunctor.map (f.val ≫ g.val) :=
        relativeCofiberMap_inclusion (f ≫ g)
      _ = relativeCofiberInclusion X.left X.right ≫
          (cofiberEndofunctor.map f.val ≫ cofiberEndofunctor.map g.val) :=
        congrArg (fun t => relativeCofiberInclusion X.left X.right ≫ t)
          (cofiberEndofunctor.map_comp f.val g.val)
      _ = (relativeCofiberMap f ≫ relativeCofiberInclusion Y.left Y.right) ≫
          cofiberEndofunctor.map g.val :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ cofiberEndofunctor.map g.val)
          (relativeCofiberMap_inclusion f).symm)
      _ = relativeCofiberMap f ≫ (relativeCofiberMap g ≫
          relativeCofiberInclusion Z.left Z.right) :=
        (Category.assoc _ _ _).trans (congrArg (fun t => relativeCofiberMap f ≫ t)
          (relativeCofiberMap_inclusion g).symm)
      _ = _ := (Category.assoc _ _ _).symm

/-- 相対 cofiber の包含は相対入力に関して自然な完全関手。 -/
def relativeCofiberInclusionNat :
    relativeCofiberFunctor.{u} ⟶ relativeAmbientFunctor ⋙ cofiberEndofunctor where
  app X := relativeCofiberInclusion X.left X.right
  naturality {_X _Y} f := relativeCofiberMap_inclusion f

end SerrePositivity.KST.SConstruction
