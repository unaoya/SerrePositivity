module

public import SerrePositivity.KST.Comparison.MonoidComponents
public import SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroLocalization

/-!
# 単体的モノイドの連結成分の関手性

概要：単体的モノイドの射は連結成分のモノイド射を誘導し、基礎射が局所化可逆なら同型を誘導する。
方針：零次単体で積と単位の保存を確認し、既存の π₀ の局所化反転性を使う。
規約：KST Lemma 2.13、Segal 1974 Proposition 1.5 の群状性の模型に関する不変性。
使われ方：元の単体的モノイドから Kan なモノイドへ群状性を移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite SSet
open scoped Simplicial
namespace SimplicialMonoid

/--
概要：単体的モノイドの射が誘導する連結成分のモノイド射。
方針：基礎単体集合の mapπ₀ を使い、零次単体の代表元で単位と積を確認する。
規約：連結成分のモノイド構造は componentsMonoid を使う。
使われ方：群状性を置換へ移す。
-/
def componentsMap {M N : SimplicialObject MonCat.{u}} (f : M ⟶ N) :
    letI := componentsMonoid M
    letI := componentsMonoid N
    π₀ (monoidSpace M) →* π₀ (monoidSpace N) := by
  letI := componentsMonoid M
  letI := componentsMonoid N
  letI : Monoid ((monoidSpace M).obj (op ⦋0⦌)) := inferInstanceAs (Monoid (M.obj (op ⦋0⦌)))
  letI : Monoid ((monoidSpace N).obj (op ⦋0⦌)) := inferInstanceAs (Monoid (N.obj (op ⦋0⦌)))
  refine
    { toFun := mapπ₀ (Functor.whiskerRight f (forget MonCat))
      map_one' := ?_
      map_mul' := ?_ }
  · change π₀.mk (X := monoidSpace N) ((f.app (op ⦋0⦌)) (1 : M.obj (op ⦋0⦌))) = π₀.mk (X := monoidSpace N) (1 : N.obj (op ⦋0⦌))
    exact congrArg (π₀.mk (X := monoidSpace N)) (map_one (f.app (op ⦋0⦌)).hom)
  · intro a b
    induction a using π₀.rec with | mk a => ?_
    induction b using π₀.rec with | mk b => ?_
    change π₀.mk (X := monoidSpace N) ((f.app (op ⦋0⦌)) (a * b)) =
      π₀.mk (X := monoidSpace N) ((f.app (op ⦋0⦌)) a * (f.app (op ⦋0⦌)) b)
    exact congrArg (π₀.mk (X := monoidSpace N)) (map_mul (f.app (op ⦋0⦌)).hom a b)

/--
概要：π₀ 上で全射な単体的モノイドの射は、元の群状性を値域へ移す。
方針：各成分を元の成分の像として表し、その単元性をモノイド射で送る。
規約：各次数の逆元を要求しない群状モノイドの条件。
使われ方：Kan な置換の群状性。
-/
theorem isGrouplike_of_components_surjective {M N : SimplicialObject MonCat.{u}} (f : M ⟶ N)
    (hM : IsGrouplike M) (hf : Function.Surjective (componentsMap f)) : IsGrouplike N := by
  let := componentsMonoid M
  let := componentsMonoid N
  intro b
  obtain ⟨a, rfl⟩ := hf b
  exact (hM a).map (componentsMap f)

/--
概要：基礎射が anodyne 局所化で可逆なら、連結成分のモノイドは同型になる。
方針：連結成分のモノイド射と、既存の局所化による π₀ の全単射の定理を使う。
規約：KST Lemma 2.13 の模型の移行。
使われ方：元と Kan なモノイドの π₀ の群状性を比較する。
-/
def componentsMulEquiv {M N : SimplicialObject MonCat.{u}} (f : M ⟶ N)
    (hf : IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (Functor.whiskerRight f (forget MonCat)))) :
    letI := componentsMonoid M
    letI := componentsMonoid N
    π₀ (monoidSpace M) ≃* π₀ (monoidSpace N) := by
  letI := componentsMonoid M
  letI := componentsMonoid N
  exact MulEquiv.ofBijective (componentsMap f)
    (SerrePositivity.SimplicialModel.PiZeroLocalization.piZero_bijective _ hf)

end SimplicialMonoid
end SerrePositivity.KST.Comparison
