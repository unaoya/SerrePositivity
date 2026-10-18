module

public import SerrePositivity.KST.Descent.OrbitAction
public import SerrePositivity.KST.Descent.CopyComparison

/-!
# 軌道の非交和の成分と fold の指定比較

## 概要
W = ⊔_I B の各包含を有限型の圏内に構成し、軌道射との合成、fold、コピーの置換と両立させる。

## 方針
標準の非交和の包含を基底上の射にする。
各包含と自己同型の合成を検査し、前層のコピー比較の定理を適用する。

## 規約
非交和の前層比較の全単射性は、Zariski 降下から供給すべき条件として明示する。
この条件だけを (1) の全ての内容とはしない。

## 使われ方
論文 (3.8) のコピー側の比較を、実際の有限型スキームの射へ接続する。
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {B V : FiniteTypeSchemes S} {I : Type u} [Finite I]
variable (p : V ⟶ B) [IsSeparated p.hom.left]
variable (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B)

/-- 概要：軌道の非交和への各コピーの包含（論文 (3.8)）。
方針：標準の非交和の包含を、切断の構造射との可換性で基底上の射にする。
規約：前層 L の定義域内の射。
使われ方：非交和の値から各コピーの値への指定引き戻し。 -/
noncomputable def orbitComponent (i : I) : B ⟶ orbitSource p sections section_identity :=
  ObjectProperty.homMk (Over.homMk (Sigma.ι (fun _ : I ↦ B.obj.left) i) (by
    change Sigma.ι (fun _ : I ↦ B.obj.left) i ≫
      (sectionOrbitMap (fun i ↦ (sections i).hom.left) ≫ V.obj.hom) = B.obj.hom
    rw [sectionOrbitMap_component_assoc, (sections i).hom.w]))

/-- 概要：コピーの包含と軌道射の合成は指定切断（論文 定理 3.1）。
方針：忘却後に非交和の包含の公式を使う。
規約：各コピーの射を選び直さない。
使われ方：fold と前層の対角比較の整合性。 -/
@[reassoc (attr := simp)] theorem orbitComponent_morphism (i : I) :
    orbitComponent p sections section_identity i ≫ orbitMorphism p sections section_identity =
      sections i := by
  apply ObjectProperty.hom_ext
  apply (Over.forget S).map_injective
  exact sectionOrbitMap_component _ i

/-- 概要：非交和 W から一つのコピー B への fold（論文 (3.8)）。
方針：軌道射と V → B を合成する。
規約：軌道の比較立方体の右上の射と同じ合成。
使われ方：コピーの置換不変部分への降下比較。 -/
noncomputable def orbitFold : orbitSource p sections section_identity ⟶ B :=
  orbitMorphism p sections section_identity ≫ p

/-- 概要：各コピーへの fold の制限は恒等射（論文 (3.8)）。
方針：軌道射の成分の公式と切断の恒等式を使う。
規約：有限型の圏内の射の等式。
使われ方：前層のコピー比較と指定対角写像の一致。 -/
@[reassoc (attr := simp)] theorem orbitComponent_fold (i : I) :
    orbitComponent p sections section_identity i ≫ orbitFold p sections section_identity = 𝟙 B := by
  rw [orbitFold, orbitComponent_morphism_assoc, section_identity i]

/-- 概要：軌道のコピーの包含は指定された添字置換と可換（論文 (3.8)）。
方針：忘却後に非交和の置換自己同型の定義を適用する。
規約：添字を g 倍する左作用。
使われ方：前層のコピー比較の置換表現への同変性。 -/
theorem orbitComponent_action {G : Type*} [Group G] [MulAction G I]
    (action : G →* Aut V)
    (equivariant : ∀ g i, sections (g • i) = sections i ≫ (action g).asIso.hom)
    (g : G) (i : I) :
    orbitComponent p sections section_identity i ≫
        (orbitAction p sections section_identity action equivariant g).asIso.hom =
      orbitComponent p sections section_identity (g • i) := by
  apply ObjectProperty.hom_ext
  apply (Over.forget S).map_injective
  change Sigma.ι (fun _ : I ↦ B.obj.left) i ≫
      (sectionOrbitPermutation (I := I) B.obj.left g).hom =
    Sigma.ι (fun _ : I ↦ B.obj.left) (g • i)
  simp [sectionOrbitPermutation]

/-- 概要：コピーの置換作用の下で fold は不変（論文 (3.8)）。
方針：軌道射の同変性と V → B の不変性を合成する。
規約：B の作用は自明。
使われ方：fold の指定された不変部分への比較の定義。 -/
theorem orbitFold_invariant {G : Type*} [Group G] [MulAction G I]
    (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (equivariant : ∀ g i, sections (g • i) = sections i ≫ (action g).asIso.hom) (g : G) :
    (orbitAction p sections section_identity action equivariant g).asIso.hom ≫
        orbitFold p sections section_identity = orbitFold p sections section_identity := by
  rw [orbitFold, ← Category.assoc, orbitMorphism_equivariant, Category.assoc, over_base g]

/-- 概要：実際の非交和のコピー比較から fold の全次数降下（論文 (3.8)）。
方針：指定包含・置換・fold の幾何的な可換式を、前層のコピー比較の定理へ入力する。
規約：前層の非交和比較の全単射性は明示し、実際の Zariski 降下からの供給は残す。
使われ方：軌道正方形の中項のコピー側の同型性。 -/
theorem orbitFold_piDescent_of_evaluation {Coefficient : Type w}
    (L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient)
    {G : Type*} [Group G] [Finite G] [MulAction G I]
    [MulAction.IsPretransitive G I] [Nonempty I]
    (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (equivariant : ∀ g i, sections (g • i) = sections i ≫ (action g).asIso.hom)
    (evaluation_bijective : ∀ H n, Function.Bijective
      (L.copyEvaluation H n (orbitComponent p sections section_identity))) :
    L.PiDescent (orbitFold p sections section_identity)
      (orbitAction p sections section_identity action equivariant)
      (orbitFold_invariant p sections section_identity action over_base equivariant) :=
  L.copyFold_piDescent_of_evaluation (orbitComponent p sections section_identity)
    (orbitFold p sections section_identity) (orbitComponent_fold p sections section_identity)
    (orbitAction p sections section_identity action equivariant)
    (orbitComponent_action p sections section_identity action equivariant)
    (orbitFold_invariant p sections section_identity action over_base equivariant)
    evaluation_bijective

end SerrePositivity.KST.Descent
