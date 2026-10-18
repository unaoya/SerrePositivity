module

public import SerrePositivity.KST.Comparison.LocalCoefficients

/-!
# 宇宙を保つ整数係数と自由アーベル群

概要：一点上の自由アーベル群を整数係数の宇宙を保つ模型とする。
方針：整数との加法同値を明示し、その直和を自由アーベル群と比較する。
規約：Weibel K-book IV.1.6 の定数整数局所係数。
使われ方：局所係数の複体と整数鎖複体の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits

/--
概要：指定宇宙に属する整数係数群。
方針：一点の自由アーベル群を取る。
規約：整数との加法同値を明示する。
使われ方：定数整数局所係数。
-/
def integerCoefficientGroup : AddCommGrpCat.{u} := AddCommGrpCat.free.obj PUnit.{u + 1}

/--
概要：整数係数群と通常の整数群の加法同値。
方針：一点上の自由アーベル群の標準同値を使う。
規約：元の型の宇宙は異なってよい。
使われ方：整数係数であることの保証。
-/
def integerCoefficientGroupEquiv : integerCoefficientGroup.{u} ≃+ ℤ :=
  FreeAbelianGroup.uniqueEquiv PUnit

/--
概要：一点の自由アーベル群の生成元を指定の元へ送る準同型。
方針：定数の型の写像へ自由関手を適用する。
規約：任意の型 T の元を指定する。
使われ方：整数直和から自由群への比較。
-/
def integerGeneratorMap {T : Type u} (t : T) :
    integerCoefficientGroup.{u} ⟶ AddCommGrpCat.free.obj T :=
  AddCommGrpCat.free.map (↾fun _ => t)

/--
概要：T 個の整数係数群の直和と T 上の自由アーベル群の同型。
方針：生成元を対応させ、両逆写像を自由群の普遍性で作る。
規約：全ての型 T に対する実際の群同型。
使われ方：整数定数局所係数の鎖群の計算。
-/
def integerCoefficientCoproductIso (T : Type u) :
    (∐ fun _ : T => integerCoefficientGroup.{u}) ≅ AddCommGrpCat.free.obj T where
  hom := Sigma.desc (fun t => integerGeneratorMap t)
  inv := AddCommGrpCat.ofHom (FreeAbelianGroup.lift (fun t =>
    (Sigma.ι (fun _ : T => integerCoefficientGroup.{u}) t) (FreeAbelianGroup.of PUnit.unit)))
  hom_inv_id := by
    apply Sigma.hom_ext
    intro t
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro p
    cases p
    simp [integerGeneratorMap, AddCommGrpCat.free_map, FreeAbelianGroup.map_of_apply,
      FreeAbelianGroup.lift_apply_of]
    rfl
  inv_hom_id := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro t
    let H : (∐ fun _ : T => integerCoefficientGroup.{u}) ⟶ AddCommGrpCat.free.obj T :=
      Sigma.desc (fun t => integerGeneratorMap t)
    have hl : (FreeAbelianGroup.lift (fun t =>
        (Sigma.ι (fun _ : T => integerCoefficientGroup.{u}) t)
          (FreeAbelianGroup.of PUnit.unit))) (FreeAbelianGroup.of t) =
        (Sigma.ι (fun _ : T => integerCoefficientGroup.{u}) t)
          (FreeAbelianGroup.of PUnit.unit) := FreeAbelianGroup.lift_apply_of _ t
    change H.hom ((FreeAbelianGroup.lift (fun t =>
      (Sigma.ι (fun _ : T => integerCoefficientGroup.{u}) t)
        (FreeAbelianGroup.of PUnit.unit))) (FreeAbelianGroup.of t)) = FreeAbelianGroup.of t
    calc
      _ = H.hom ((Sigma.ι (fun _ : T => integerCoefficientGroup.{u}) t)
          (FreeAbelianGroup.of PUnit.unit)) := congrArg H.hom hl
      _ = (integerGeneratorMap t).hom (FreeAbelianGroup.of PUnit.unit) :=
        congrArg (fun q : integerCoefficientGroup.{u} ⟶ AddCommGrpCat.free.obj T =>
          q.hom (FreeAbelianGroup.of PUnit.unit))
          (Sigma.ι_comp_desc (fun t => integerGeneratorMap t) t)
      _ = FreeAbelianGroup.of t := FreeAbelianGroup.map_of_apply _

end SerrePositivity.KST.Comparison
