module

public import SerrePositivity.KST.Descent.OrbitCopies
public import SerrePositivity.KST.Descent.CopyEvaluationLimit

/-!
# 有限型の圏内の軌道の非交和の普遍性

## 概要
W = ⊔_I B と指定された成分が、前層の定義域である有限型の圏内でも非交和を与える。
この普遍性を、積を保つ前層のコピー比較へ接続する。

## 方針
スキームの非交和の desc を基底上の射へ持ち上げ、その一意性を忘却で検査する。
反対圏の積に前層を適用して指定比較の全単射性を得る。

## 規約
有限型の圏内の全ての余極限の存在を仮定しない。
前層の有限積保存は実際の Zariski 降下から供給すべき別の条件。

## 使われ方
論文 (3.8) のコピーの置換不変部分を実際の幾何学的な fold へ接続する。
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {B V : FiniteTypeSchemes S} {I : Type u} [Finite I]
variable (p : V ⟶ B) [IsSeparated p.hom.left]
variable (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B)

/-- 概要：軌道のコピーの任意の cofan への指定射（論文 (3.8)）。
方針：スキームの非交和の desc を、各成分の構造射の可換性で持ち上げる。
規約：有限型の圏内の射として構成する。
使われ方：軌道の非交和の普遍性の存在部分。 -/
noncomputable def orbitCoproductDesc (s : Cofan (fun _ : I ↦ B)) :
    orbitSource p sections section_identity ⟶ s.pt :=
  ObjectProperty.homMk (Over.homMk (Sigma.desc fun i ↦ (s.inj i).hom.left) (by
    change (Sigma.desc fun i ↦ (s.inj i).hom.left) ≫ s.pt.obj.hom =
      sectionOrbitMap (fun i ↦ (sections i).hom.left) ≫ V.obj.hom
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc_assoc, sectionOrbitMap_component_assoc,
      (s.inj i).hom.w, (sections i).hom.w]))

/-- 概要：軌道 W と指定包含は有限型の圏内で非交和（論文 (3.8)）。
方針：基底上に持ち上げた desc と、その各成分での式・一意性を検査する。
規約：単なる忘却後の非交和の宣言ではない。
使われ方：前層の積保存からコピー比較の全単射性を導く。 -/
noncomputable def orbitSourceIsCoproduct :
    IsColimit (Cofan.mk (orbitSource p sections section_identity)
      (orbitComponent p sections section_identity)) := by
  refine Cofan.IsColimit.mk _ (orbitCoproductDesc p sections section_identity) ?_ ?_
  · intro s i
    apply ObjectProperty.hom_ext
    apply (Over.forget S).map_injective
    exact Sigma.ι_comp_desc _ i
  · intro s m hm
    apply ObjectProperty.hom_ext
    apply (Over.forget S).map_injective
    apply Sigma.hom_ext
    intro i
    have h := congrArg (fun k ↦ k.hom.left) (hm i)
    exact h.trans (Sigma.ι_comp_desc (fun j ↦ (s.inj j).hom.left) i).symm

/-- 概要：積を保つ前層の軌道コピー比較は全単射（論文 (3.8)）。
方針：有限型の圏内で証明した非交和の普遍性を前層の積保存に適用する。
規約：必要なのはこの有限個のコピーの積の保存であり、全ての極限の保存ではない。
使われ方：実際の fold の全次数降下への入力。 -/
theorem orbitCopyEvaluation_bijective_of_preservesProduct {Coefficient : Type w}
    (L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient)
    (H : Coefficient) (n : ℤ)
    [PreservesLimit (Discrete.functor (fun _ : I ↦ op B)) (L H n)] :
    Function.Bijective (L.copyEvaluation H n (orbitComponent p sections section_identity)) :=
  L.copyEvaluation_bijective_of_preservesProduct H n (orbitComponent p sections section_identity)
    (orbitSourceIsCoproduct p sections section_identity)

/-- 概要：各次数でコピーの積を保つ前層の実際の fold の全次数降下（論文 (3.8)）。
方針：軌道の非交和の普遍性でコピー比較の全単射性を証明し、対角比較の定理を使う。
規約：この積保存は有限非交和の降下の帰結として供給する条件。
使われ方：軌道正方形の中項のコピー側の比較の完成。 -/
theorem orbitFold_piDescent_of_preservesProduct {Coefficient : Type w}
    (L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient)
    [∀ H n, PreservesLimit (Discrete.functor (fun _ : I ↦ op B)) (L H n)]
    {G : Type*} [Group G] [Finite G] [MulAction G I]
    [MulAction.IsPretransitive G I] [Nonempty I]
    (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (equivariant : ∀ g i, sections (g • i) = sections i ≫ (action g).asIso.hom) :
    L.PiDescent (orbitFold p sections section_identity)
      (orbitAction p sections section_identity action equivariant)
      (orbitFold_invariant p sections section_identity action over_base equivariant) :=
  orbitFold_piDescent_of_evaluation p sections section_identity L action over_base equivariant
    (fun H n ↦ orbitCopyEvaluation_bijective_of_preservesProduct p sections section_identity L H n)

end SerrePositivity.KST.Descent
