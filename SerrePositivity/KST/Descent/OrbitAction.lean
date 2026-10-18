module

public import SerrePositivity.KST.Descent.OrbitGeometry

/-!
# 有限型の圏内の軌道射の G 作用

## 概要
コピーの置換作用を有限型の圏内へ持ち上げ、指定された軌道射の同変性を証明する。

## 方針
section の族の同変性から非交和の自己同型が基底の構造射を保つことを示す。
自己同型と群の法則を実際のスキームの射へ忘却して検査する。

## 規約
被約な中心や境界の同変性はこの作用の構成に含めない。
始域のコピーの各 B には自明に作用し、添字だけを置換する。

## 使われ方
論文 定理 3.1 の G 同変な軌道正方形、および (3.8) の幾何的な置換作用。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {B V : FiniteTypeSchemes S} {I : Type u} [Finite I]
variable {G : Type*} [Group G] [MulAction G I]

/-- 概要：軌道射のスキームとしての同変性を有限型の作用から得る（論文 (3.7)）。
方針：有限型の圏を忘却して、構成済みの非交和の作用の補題に適用する。
規約：指定された切断と自己同型の値を保持する。
使われ方：コピーの置換が基底上の自己同型であることの検証。 -/
theorem orbitMorphism_raw_equivariant (p : V ⟶ B) [IsSeparated p.hom.left]
    (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B)
    (action : G →* Aut V)
    (equivariant : ∀ g i, sections (g • i) = sections i ≫ (action g).asIso.hom) (g : G) :
    (sectionOrbitAction (I := I) G B.obj.left g).asIso.hom ≫
        (orbitMorphism p sections section_identity).hom.left =
      (orbitMorphism p sections section_identity).hom.left ≫ (action g).asIso.hom.hom.left := by
  exact sectionOrbitMap_equivariant (fun i ↦ (sections i).hom.left)
    ((Functor.mapAut V (finiteTypeSchemesForget S)).comp action)
    (fun g i ↦ congrArg (fun k ↦ k.hom.left) (equivariant g i)) g

/-- 概要：コピーの置換を有限型の圏内の自己同型にする（論文 定理 3.1）。
方針：軌道射の同変性と V の基底上の作用から構造射の保存を示す。
規約：元の非交和の置換と同じスキームの自己同型。
使われ方：前層 L を適用する圏内の G 作用。 -/
noncomputable def orbitPermutation (p : V ⟶ B) [IsSeparated p.hom.left]
    (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B)
    (action : G →* Aut V)
    (equivariant : ∀ g i, sections (g • i) = sections i ≫ (action g).asIso.hom) (g : G) :
    orbitSource p sections section_identity ≅ orbitSource p sections section_identity :=
  ObjectProperty.isoMk _ (Over.isoMk (sectionOrbitPermutation (I := I) B.obj.left g) (by
    change (sectionOrbitAction (I := I) G B.obj.left g).asIso.hom ≫
        (sectionOrbitMap (fun i ↦ (sections i).hom.left) ≫ V.obj.hom) =
      sectionOrbitMap (fun i ↦ (sections i).hom.left) ≫ V.obj.hom
    have h := sectionOrbitMap_equivariant (fun i ↦ (sections i).hom.left)
      ((Functor.mapAut V (finiteTypeSchemesForget S)).comp action)
      (fun g i ↦ congrArg (fun k ↦ k.hom.left) (equivariant g i)) g
    rw [← Category.assoc, h, Category.assoc]
    change sectionOrbitMap (fun i ↦ (sections i).hom.left) ≫
        ((action g).asIso.hom.hom.left ≫ V.obj.hom) = _
    rw [(action g).asIso.hom.hom.w]))

/-- 概要：有限型の圏内でのコピーの置換の G 作用（論文 定理 3.1）。
方針：スキームの非交和の作用の群の法則を忠実な忘却で反映する。
規約：源の作用を任意に選ばず、指定された添字の作用から構成する。
使われ方：前層 L の置換表現と軌道射の同変比較。 -/
noncomputable def orbitAction (p : V ⟶ B) [IsSeparated p.hom.left]
    (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B)
    (action : G →* Aut V)
    (equivariant : ∀ g i, sections (g • i) = sections i ≫ (action g).asIso.hom) :
    G →* Aut (orbitSource p sections section_identity) where
  toFun g := Aut.of (orbitPermutation p sections section_identity action equivariant g)
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply ObjectProperty.hom_ext
    apply (Over.forget S).map_injective
    exact congrArg (fun a ↦ a.asIso.hom) (sectionOrbitAction (I := I) G B.obj.left).map_one
  map_mul' g h := by
    apply Aut.ext
    apply Iso.ext
    apply ObjectProperty.hom_ext
    apply (Over.forget S).map_injective
    exact congrArg (fun a ↦ a.asIso.hom) ((sectionOrbitAction (I := I) G B.obj.left).map_mul g h)

/-- 概要：有限型の圏内の軌道射は構成した G 作用について同変（論文 定理 3.1）。
方針：スキームの射へ忘却して構成済みの指定可換式を使う。
規約：前層 L の反変性を適用できる圏内の等式。
使われ方：軌道正方形の G 同変な制限と差の写像。 -/
theorem orbitMorphism_equivariant (p : V ⟶ B) [IsSeparated p.hom.left]
    (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B)
    (action : G →* Aut V)
    (equivariant : ∀ g i, sections (g • i) = sections i ≫ (action g).asIso.hom) (g : G) :
    (orbitAction p sections section_identity action equivariant g).asIso.hom ≫
        orbitMorphism p sections section_identity =
      orbitMorphism p sections section_identity ≫ (action g).asIso.hom := by
  apply ObjectProperty.hom_ext
  apply (Over.forget S).map_injective
  exact orbitMorphism_raw_equivariant p sections section_identity action equivariant g

end SerrePositivity.KST.Descent
