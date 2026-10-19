module

public import SerrePositivity.KST.Comparison.FiberCoefficientAdjunction
public import Mathlib.CategoryTheory.Limits.MonoCoprod

/-!
# 係数の直和関手の成分と単射保存

概要：基底上の係数の直和関手の射を計算し、単射を保存することを証明する。
方針：各成分の標準輸送と添字集合の単射による直和の包含へ分解する。
規約：Weibel K-book IV.1.6 の局所係数の次数ごとの模型。
使われ方：単射なセル添付の局所係数鎖複体。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits

/--
概要：基底上の型の射の可換性の元ごとの式。
方針：可換三角形を元で評価する。
規約：像の基底点は元の基底点と一致する。
使われ方：係数群の等式の輸送。
-/
theorem overTypeMap_base {T : Type u} {p q : Over T} (f : p ⟶ q) (x : p.left) :
    q.hom (f.left x) = p.hom x := congrArg (fun h : p.left ⟶ T => h x) f.w

/--
概要：係数直和関手の写像は各成分を対応する像の成分へ送る。
方針：随伴から作った関手の定義と直和の因子分解式を計算する。
規約：可換性からの係数の標準輸送を明示する。
使われ方：局所係数の次数ごとの直和表示の自然性。
-/
@[reassoc] theorem fiberCoefficientFunctor_map_ι {T : Type u} (A : T → AddCommGrpCat.{u})
    {p q : Over T} (f : p ⟶ q) (x : p.left) :
    Sigma.ι (fun x : p.left => A (p.hom x)) x ≫ (fiberCoefficientFunctor T A).map f =
      eqToHom (congrArg A (overTypeMap_base f x).symm) ≫
        Sigma.ι (fun y : q.left => A (q.hom y)) (f.left x) := by
  change Sigma.ι (fun x : p.left => A (p.hom x)) x ≫
      fiberCoefficientDesc A p _ (f ≫ fiberCoefficientLift A q _ (𝟙 _)) = _
  dsimp only [fiberCoefficientDesc]
  rw [Sigma.ι_comp_desc]
  change eqToHom (congrArg A (overTypeMap_base f x).symm) ≫
      (Sigma.ι (fun y : q.left => A (q.hom y)) (f.left x) ≫ 𝟙 _) = _
  rw [Category.comp_id]

/--
概要：係数直和の射は係数の標準輸送の直和と、添字の射による直和の写像の合成である。
方針：各直和成分との合成を計算する。
規約：中間の族は標的の係数群を添字の写像で引き戻したもの。
使われ方：単射な添字の写像に対する単射性。
-/
theorem fiberCoefficientFunctor_map_factorization {T : Type u}
    (A : T → AddCommGrpCat.{u}) {p q : Over T} (f : p ⟶ q) :
    (fiberCoefficientFunctor T A).map f =
      CategoryTheory.Limits.Sigma.map
        (fun x : p.left => eqToHom (congrArg A (overTypeMap_base f x).symm)) ≫
        Sigma.map' f.left (fun x : p.left => 𝟙 (A (q.hom (f.left x)))) := by
  apply Sigma.hom_ext
  intro x
  rw [fiberCoefficientFunctor_map_ι, ← Category.assoc, Sigma.ι_map,
    Category.assoc, Sigma.ι_comp_map', Category.id_comp]

/--
概要：係数群の直和を取る関手は基底上の型の単射を保存する。
方針：係数の標準輸送は同型で、添字の単射による直和の写像は単射である。
規約：係数群の平坦性は不要。
使われ方：局所係数鎖複体の単射保存。
-/
instance fiberCoefficientFunctor_preservesMonomorphisms (T : Type u)
    (A : T → AddCommGrpCat.{u}) : (fiberCoefficientFunctor T A).PreservesMonomorphisms where
  preserves {p q} f _ := by
    have hf : Function.Injective f.left :=
      (CategoryTheory.mono_iff_injective f.left).mp inferInstance
    have : Mono (Sigma.map' (f := fun y : q.left => A (q.hom y))
        (g := fun x : p.left => A (q.hom (f.left x))) f.left (fun x => 𝟙 _)) :=
      MonoCoprod.mono_map'_of_injective (fun y : q.left => A (q.hom y)) f.left hf
    rw [fiberCoefficientFunctor_map_factorization]
    infer_instance

end SerrePositivity.KST.Comparison
