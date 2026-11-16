module

public import SerrePositivity.InfinityCategories.Sheaves.CechCommaPrefix

/-!
概要：Čech comma の恒等関手と根から、同じ prefix 関手への自然変換を作る。
方針：元の座標を選ぶ tail と、根の零座標を選ぶ定値作用素を用いる。
  文献対応：HTT 4.1.3.1、Kerodon Theorem 7.2.3.1（Tag 02NY）の cofinality。
規約：二つの変換を同じ収縮関手へ向ける。comma の終対象性を仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [Category.{v} C] {U V : C}

/-- 根の零次の Čech 冪への束縛。 -/
def cechCommaRoot (d : CategoryTheory.CechNerveData U) (r : V ⟶ U) : CechComma d V :=
  CostructuredArrow.mk (cechPowerLift d (n := 0) (fun _ ↦ r)).op

/-- 元の対象から同じ根を付加した対象への自然変換。 -/
def cechCommaToPrefix (d : CategoryTheory.CechNerveData U) (r : V ⟶ U) :
    𝟭 (CechComma d V) ⟶ cechCommaPrefix d r where
  app a := CostructuredArrow.homMk (simplexPrefixTail a.left) (by
    apply Quiver.Hom.unop_inj
    change cechCommaPrefixLift d r a ≫ d.obj.map (simplexPrefixTail a.left).op = a.hom.unop
    apply cechPower_hom_ext d
    intro i
    rw [Category.assoc, d.proj_map, cechCommaPrefixLift_proj]
    rfl)
  naturality {a b} f := by
    apply CostructuredArrow.hom_ext
    exact (simplexPrefixTail_naturality f.left).symm

/-- 根の対象から同じ prefix 対象への自然変換。 -/
def cechCommaRootToPrefix (d : CategoryTheory.CechNerveData U) (r : V ⟶ U) :
    (Functor.const (CechComma d V)).obj (cechCommaRoot d r) ⟶ cechCommaPrefix d r where
  app a := CostructuredArrow.homMk (SimplexCategory.const ⦋0⦌ ⦋a.left.len + 1⦌ 0) (by
    apply Quiver.Hom.unop_inj
    change cechCommaPrefixLift d r a ≫
      d.obj.map (SimplexCategory.const ⦋0⦌ ⦋a.left.len + 1⦌ 0).op =
        cechPowerLift d (n := 0) (fun _ ↦ r)
    apply cechPower_hom_ext d
    intro i
    rw [Category.assoc, d.proj_map, cechCommaPrefixLift_proj, cechPowerLift_proj]
    rfl)
  naturality {a b} f := by
    apply CostructuredArrow.hom_ext
    change (𝟙 ⦋0⦌) ≫ SimplexCategory.const ⦋0⦌ ⦋b.left.len + 1⦌ 0 =
      SimplexCategory.const ⦋0⦌ ⦋a.left.len + 1⦌ 0 ≫ simplexPrefixMap f.left
    rw [Category.id_comp, simplexPrefixMap_zero]

end SerrePositivity.InfinityCategories.Sheaves
