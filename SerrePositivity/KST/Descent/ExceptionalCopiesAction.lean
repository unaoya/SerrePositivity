module

public import SerrePositivity.KST.Descent.ExceptionalCopies

/-!
# 例外部分のコピー分解と群作用

## 概要
例外部分の実際の G 作用が、Z のコピーの添字を置換することを証明する。
前層がこの有限非交和を積へ送れば、例外部分の指定 fold は全次数の降下を満たす。

## 方針
例外部分の二射影で作用を検査し、合成引き戻しの普遍性で包含の等式を示す。
指定されたコピー評価と対角写像の比較を適用する。

## 規約
コピー分解に合わせて群作用を選び直さず、軌道正方形の実際の引き戻し作用を使う。
有限積保存は実際の Zariski 降下から供給する責務として残る。

## 使われ方
論文 定理 3.1・(3.8) の例外部分の固定比較。
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {B V : FiniteTypeSchemes S} {I : Type u} [Finite I]
variable (p : V ⟶ B) [IsSeparated p.hom.left] [IsSeparated V.obj.hom]
variable (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B)
variable {G : Type*} [Group G] [MulAction G I]
variable (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
variable (equivariant : ∀ g i, sections (g • i) = sections i ≫ (action g).asIso.hom)

set_option quotPrecheck false in
local notation "Z₀" =>
  reducedClosedAsFiniteType B (coincidenceClosedSet (fun i ↦ (sections i).hom))
set_option quotPrecheck false in
local notation "z₀" =>
  reducedClosedAsFiniteTypeInclusion B (coincidenceClosedSet (fun i ↦ (sections i).hom))
set_option quotPrecheck false in
local notation "c₀" =>
  closedCenterPullbackFirst p (coincidenceClosedSet (fun i ↦ (sections i).hom))
set_option quotPrecheck false in
local notation "c₁" =>
  closedCenterPullbackSecond p (coincidenceClosedSet (fun i ↦ (sections i).hom))
local notation "q₀" => orbitMorphism p sections section_identity
local notation "aW" => orbitAction p sections section_identity action equivariant
local notation "aC" => orbitCenterAction p sections action over_base

/-- 概要：例外部分の実際の引き戻しの G 作用（論文 定理 3.1）。
方針：W、V ×_B Z、V の既存の作用から閉中心の引き戻しの作用を構成する。
規約：軌道正方形の左上の作用と同じ構成。
使われ方：Z のコピーの添字置換との両立。 -/
noncomputable def orbitExceptionalAction :
    G →* Aut (orbitExceptionalSource p sections section_identity) :=
  closedPullbackAction q₀ c₀ aW aC action
    (orbitMorphism_equivariant p sections section_identity action equivariant)
    (orbitCenterInclusion_equivariant p sections action over_base)

/-- 概要：例外部分から W への射影は同変（論文 定理 3.1）。
方針：閉中心の引き戻しの第一射影の同変性を適用する。
規約：W の指定されたコピーの置換作用を使う。
使われ方：例外部分のコピーの包含の作用を第一射影で検査する。 -/
theorem orbitExceptionalAction_source (g : G) :
    (orbitExceptionalAction p sections section_identity action over_base equivariant g).asIso.hom ≫
        orbitExceptionalToSource p sections section_identity =
      orbitExceptionalToSource p sections section_identity ≫ (aW g).asIso.hom :=
  closedPullbackAction_fst q₀ c₀ aW aC action
    (orbitMorphism_equivariant p sections section_identity action equivariant)
    (orbitCenterInclusion_equivariant p sections action over_base) g

/-- 概要：例外部分から Z への指定 fold は作用で不変（論文 (3.8)）。
方針：第二射影の同変性と、V ×_B Z → Z の不変性を合成する。
規約：Z には自明に作用する。
使われ方：例外部分の降下比較を定義する。 -/
theorem orbitExceptionalProjection_invariant (g : G) :
    (orbitExceptionalAction p sections section_identity action over_base equivariant g).asIso.hom ≫
        orbitExceptionalProjection p sections section_identity =
      orbitExceptionalProjection p sections section_identity := by
  have h := closedPullbackAction_snd q₀ c₀ aW aC action
    (orbitMorphism_equivariant p sections section_identity action equivariant)
    (orbitCenterInclusion_equivariant p sections action over_base) g
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k ↦ k ≫ c₁) h).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun k ↦ (closedImmersionSquare q₀ c₀).f₁₃ ≫ k)
          (orbitCenterProjection_invariant p sections action over_base g))))

/-- 概要：例外部分の既存の作用は Z のコピーを添字で置換する（論文 (3.8)）。
方針：W への射影と Z への fold の二つで等式を検査する。
規約：群作用は分解に合わせた別の作用ではなく、実際の引き戻し作用。
使われ方：例外部分の前層のコピー比較の同変性。 -/
theorem orbitExceptionalComponent_action (g : G) (i : I) :
    orbitExceptionalComponent p sections section_identity i ≫
        (orbitExceptionalAction p sections section_identity
          action over_base equivariant g).asIso.hom =
      orbitExceptionalComponent p sections section_identity (g • i) := by
  apply (orbitExceptional_isPullback p sections section_identity).hom_ext
  · rw [Category.assoc, orbitExceptionalAction_source, ← Category.assoc,
      orbitExceptionalComponent_source, Category.assoc, orbitComponent_action,
      orbitExceptionalComponent_source]
  · rw [Category.assoc, orbitExceptionalProjection_invariant,
      orbitExceptionalComponent_projection, orbitExceptionalComponent_projection]

/-- 概要：コピーの有限積を保つ前層の例外部分の全次数降下（論文 定理 3.1・(3.8)）。
方針：例外部分の実際の非交和と、コピーを置換する既存の作用に対角比較を適用する。
規約：有限積保存の実降下からの供給は残すが、例外部分の同型性自体は仮定しない。
使われ方：実際の軌道比較の例外部分の固定比較。 -/
theorem orbitExceptional_piDescent_of_preservesProduct {Coefficient : Type w}
    (L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient)
    [∀ H n, PreservesLimit (Discrete.functor (fun _ : I ↦ op Z₀)) (L H n)]
    [Finite G] [MulAction.IsPretransitive G I] [Nonempty I] :
    L.PiDescent (orbitExceptionalProjection p sections section_identity)
      (orbitExceptionalAction p sections section_identity action over_base equivariant)
      (orbitExceptionalProjection_invariant p sections section_identity
        action over_base equivariant) := by
  apply L.copyFold_piDescent_of_evaluation (orbitExceptionalComponent p sections section_identity)
    (orbitExceptionalProjection p sections section_identity)
    (orbitExceptionalComponent_projection p sections section_identity)
    (orbitExceptionalAction p sections section_identity action over_base equivariant)
    (orbitExceptionalComponent_action p sections section_identity action over_base equivariant)
    (orbitExceptionalProjection_invariant p sections section_identity action over_base equivariant)
  intro H n
  exact L.copyEvaluation_bijective_of_preservesProduct H n
    (orbitExceptionalComponent p sections section_identity)
    (orbitExceptionalIsCoproduct p sections section_identity)

end SerrePositivity.KST.Descent
