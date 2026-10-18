module

public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise

/-!
概要：全部分複体を標的とする内部 Hom の全部分複体表示。
方針：関手の頂点での条件を評価に移し、内部 Hom の評価を全部分複体に持ち上げる。
規約：quasicategory 性を要求しない。
使われ方：Kerodon §4.5.3、§4.5.5 の可逆な path と関手単体集合の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：関手単体集合の頂点が全ての頂点を指定された部分に写すという条件。
方針：各頂点での評価の像に元の条件を課す。
規約：K と Y は任意の単体集合。
使われ方：Kerodon §4.5.3 の全部分複体と内部 Hom。 -/
def FunctorVertexSatisfies (K Y : SSet.{u}) (P : Y _⦋0⦌ → Prop)
    (v : ((ihom K).obj Y) _⦋0⦌) : Prop :=
  ∀ k : K _⦋0⦌, P ((evaluateFunctorAt (Y := Y) k).app (Opposite.op ⦋0⦌) v)

/-- 概要：全部分複体への関手は全頂点で元の部分条件を満たす。
方針：各関手の頂点を実際の射で表し、評価を計算する。
規約：元の集合 P に閉性の条件は不要。
使われ方：Kerodon §4.5.3 の内部 Hom の全部分複体表示。 -/
noncomputable def fullSubcomplexInternalHomForward (K Y : SSet.{u}) (P : Y _⦋0⦌ → Prop) :
    (ihom K).obj (fullSubcomplexOnVertices Y P : SSet.{u}) ⟶
      (fullSubcomplexOnVertices ((ihom K).obj Y) (FunctorVertexSatisfies K Y P) : SSet.{u}) :=
  fullSubcomplexLift (FunctorVertexSatisfies K Y P)
    ((ihom K).map (fullSubcomplexOnVertices Y P).ι) (by
      intro v
      obtain ⟨f, rfl⟩ := (functorVertexEquiv K _).surjective v
      intro k
      have he : ((ihom K).map (fullSubcomplexOnVertices Y P).ι).app (Opposite.op ⦋0⦌)
          (functorVertex f) = functorVertex (f ≫ (fullSubcomplexOnVertices Y P).ι) := rfl
      change P ((evaluateFunctorAt (Y := Y) k).app (Opposite.op ⦋0⦌)
        (((ihom K).map (fullSubcomplexOnVertices Y P).ι).app (Opposite.op ⦋0⦌) (functorVertex f)))
      rw [he, evaluateFunctorAt_functorVertex]
      exact fullSubcomplexOnVertices_vertex (f.app (Opposite.op ⦋0⦌) k))

/-- 概要：全部分複体条件を持つ関手の評価は元の全部分複体へ持ち上がる。
方針：条件を各組の頂点で読んで評価の射に適用する。
規約：評価の始域は K と関手の部分複体の直積。
使われ方：Kerodon §4.5.3 の内部 Hom の逆向きの比較。 -/
noncomputable def fullSubcomplexInternalHomUncurry (K Y : SSet.{u}) (P : Y _⦋0⦌ → Prop) :
    K ⊗ (fullSubcomplexOnVertices ((ihom K).obj Y) (FunctorVertexSatisfies K Y P) : SSet.{u}) ⟶
      (fullSubcomplexOnVertices Y P : SSet.{u}) :=
  fullSubcomplexLift P
    ((K ◁ (fullSubcomplexOnVertices ((ihom K).obj Y) (FunctorVertexSatisfies K Y P)).ι) ≫
      (ihom.ev K).app Y) (by
      rintro ⟨k, v⟩
      have hv := fullSubcomplexOnVertices_vertex v
      change FunctorVertexSatisfies K Y P v.val at hv
      have he : ((K ◁ (fullSubcomplexOnVertices ((ihom K).obj Y)
          (FunctorVertexSatisfies K Y P)).ι) ≫ (ihom.ev K).app Y).app (Opposite.op ⦋0⦌) (k, v) =
          (evaluateFunctorAt (Y := Y) k).app (Opposite.op ⦋0⦌) v.val := by
        change v.val.app (Opposite.op ⦋0⦌) (𝟙 _) k =
          v.val.app (Opposite.op ⦋0⦌) (𝟙 _) (PinchedHom.constant k 0)
        rw [pinchedConstant_zero]
      exact he.symm ▸ hv k)

/-- 概要：頂点条件を満たす関手の族を全部分複体への関手の族へ戻す。
方針：持ち上げた評価を curry する。
規約：P は任意の頂点条件。
使われ方：Kerodon §4.5.3 の内部 Hom の逆向きの比較。 -/
noncomputable def fullSubcomplexInternalHomBackward (K Y : SSet.{u}) (P : Y _⦋0⦌ → Prop) :
    (fullSubcomplexOnVertices ((ihom K).obj Y) (FunctorVertexSatisfies K Y P) : SSet.{u}) ⟶
      (ihom K).obj (fullSubcomplexOnVertices Y P : SSet.{u}) :=
  curry (fullSubcomplexInternalHomUncurry K Y P)

/-- 概要：順方向の比較を含めると元の内部 Hom の包含になる。
方針：全部分複体への持ち上げの計算を使う。
規約：元の関手は変更しない。
使われ方：Kerodon §4.5.3 の比較の逆性。 -/
lemma fullSubcomplexInternalHomForward_ι (K Y : SSet.{u}) (P : Y _⦋0⦌ → Prop) :
    fullSubcomplexInternalHomForward K Y P ≫
      (fullSubcomplexOnVertices ((ihom K).obj Y) (FunctorVertexSatisfies K Y P)).ι =
        (ihom K).map (fullSubcomplexOnVertices Y P).ι := fullSubcomplexLift_ι _ _ _

/-- 概要：逆方向の比較を含めると条件を忘れた元の関手の族になる。
方針：uncurry し、持ち上げた評価と元の評価を比較する。
規約：厳密な等式。
使われ方：Kerodon §4.5.3 の比較の逆性。 -/
lemma fullSubcomplexInternalHomBackward_ι (K Y : SSet.{u}) (P : Y _⦋0⦌ → Prop) :
    fullSubcomplexInternalHomBackward K Y P ≫ (ihom K).map (fullSubcomplexOnVertices Y P).ι =
      (fullSubcomplexOnVertices ((ihom K).obj Y) (FunctorVertexSatisfies K Y P)).ι := by
  apply uncurry_injective
  rw [uncurry_natural_right, fullSubcomplexInternalHomBackward, uncurry_curry]
  unfold fullSubcomplexInternalHomUncurry
  rw [fullSubcomplexLift_ι, uncurry_eq]

/-- 概要：全部分複体を標的とする内部 Hom は各頂点でその部分条件を満たす全部分複体と同型。
方針：持ち上げた評価による逆射を二つの包含で検査する。
規約：任意の単体集合 K、Y と頂点条件 P。
使われ方：Kerodon §4.5.3、§4.5.5 の可逆 path と内部 Hom の比較。 -/
noncomputable def fullSubcomplexInternalHomIso (K Y : SSet.{u}) (P : Y _⦋0⦌ → Prop) :
    (ihom K).obj (fullSubcomplexOnVertices Y P : SSet.{u}) ≅
      (fullSubcomplexOnVertices ((ihom K).obj Y) (FunctorVertexSatisfies K Y P) : SSet.{u}) where
  hom := fullSubcomplexInternalHomForward K Y P
  inv := fullSubcomplexInternalHomBackward K Y P
  hom_inv_id := by
    have : Mono ((ihom K).map (fullSubcomplexOnVertices Y P).ι) :=
      (ihom K).map_mono _
    apply (cancel_mono ((ihom K).map (fullSubcomplexOnVertices Y P).ι)).1
    rw [Category.assoc, fullSubcomplexInternalHomBackward_ι,
      fullSubcomplexInternalHomForward_ι, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono
      (fullSubcomplexOnVertices ((ihom K).obj Y) (FunctorVertexSatisfies K Y P)).ι).1
    rw [Category.assoc, fullSubcomplexInternalHomForward_ι,
      fullSubcomplexInternalHomBackward_ι, Category.id_comp]

/-- 概要：内部 Hom の全部分複体表示の逆射は条件を忘れる射と可換。
方針：逆射の具体的な定義の包含上の計算を使う。
規約：同型の inv を直接使う形。
使われ方：Kerodon §4.5.3 の path との比較。 -/
lemma fullSubcomplexInternalHomIso_inv_ι (K Y : SSet.{u}) (P : Y _⦋0⦌ → Prop) :
    (fullSubcomplexInternalHomIso K Y P).inv ≫ (ihom K).map (fullSubcomplexOnVertices Y P).ι =
      (fullSubcomplexOnVertices ((ihom K).obj Y) (FunctorVertexSatisfies K Y P)).ι :=
  fullSubcomplexInternalHomBackward_ι K Y P

end SerrePositivity.InfinityCategories
