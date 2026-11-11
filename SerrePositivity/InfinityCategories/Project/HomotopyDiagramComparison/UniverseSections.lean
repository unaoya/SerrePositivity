module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeSectionEquivalence

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSSetMaps

/-!
概要：切断空間の ULift と持ち上げた射影の切断空間を厳密に比較する。
方針：普遍的な切断の評価を直積の同型で持ち上げ、族の逆対応を完全忠実性で戻す。
規約：任意の射影を扱い、Kan 性や fibration 性を要求しない。
使われ方：HTT 4.2.4.1 の重み付き end の宇宙の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

variable {K E : SSet.{u}}

/-- 概要：切断空間を持ち上げたものから持ち上げた射影の切断空間への標準比較射。
方針：普遍的な評価を持ち上げ、直積の同型を前合成して切断空間へ持ち上げる。
規約：順方向の実際の評価の族を固定する。
使われ方：HTT 4.2.4.1 の Bousfield–Kan end の切断表示の宇宙の調整。 -/
noncomputable def uliftSectionsComparison (p : E ⟶ K) :
    (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections ((SSet.uliftFunctor.{v, u}).map p) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso K (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p)).inv ≫
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation p)) (by
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation_projection]
    rfl)

/-- 概要：切断の ULift 比較射を評価すると持ち上げた元の評価になる。
方針：切断空間への持ち上げの評価の式を使う。
規約：底と切断空間の直積の同型を明示する。
使われ方：HTT 4.2.4.1 の切断の族の比較の検証。 -/
lemma uliftSectionsComparison_evaluation (p : E ⟶ K) :
    ((SSet.uliftFunctor.{v, u}).obj K ◁ uliftSectionsComparison p) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation ((SSet.uliftFunctor.{v, u}).map p) =
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso K (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p)).inv ≫
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation p) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift_evaluation _ _

/-- 概要：任意の小さいパラメータからの切断の族の比較は評価の ULift と可換。
方針：標準比較の評価と直積の同型の第二因子の自然性を使う。
規約：第一因子の底は固定する。
使われ方：HTT 4.2.4.1 の切断の族の全単射の構成。 -/
lemma uliftSectionsComparison_map_evaluation (p : E ⟶ K) {A : SSet.{u}}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p) :
    ((SSet.uliftFunctor.{v, u}).obj K ◁
      ((SSet.uliftFunctor.{v, u}).map f ≫ uliftSectionsComparison p)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation ((SSet.uliftFunctor.{v, u}).map p) =
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso K A).inv ≫
      (SSet.uliftFunctor.{v, u}).map ((K ◁ f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation p) := by
  rw [whiskerLeft_comp, Category.assoc, uliftSectionsComparison_evaluation,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso_inv_whiskerLeft,
    Category.assoc, ← CategoryTheory.Functor.map_comp]

/-- 概要：持ち上げたパラメータの切断の族を元の宇宙の評価の族へ戻す。
方針：直積の同型を前合成し、ULift 関手の充満性による原像を取る。
規約：パラメータ A 自体は元の宇宙にある。
使われ方：HTT 4.2.4.1 の切断比較の逆対応の定義。 -/
noncomputable def uliftSectionsFamilyDown (p : E ⟶ K) (A : SSet.{u})
    (g : (SSet.uliftFunctor.{v, u}).obj A ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections ((SSet.uliftFunctor.{v, u}).map p)) : K ⊗ A ⟶ E :=
  (SSet.uliftFunctor.{v, u}).preimage
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso K A).hom ≫ ((SSet.uliftFunctor.{v, u}).obj K ◁ g) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation ((SSet.uliftFunctor.{v, u}).map p))

/-- 概要：元の宇宙へ戻した切断の評価の族は底を厳密に固定する。
方針：ULift の忠実性で検出し、元の切断の族の射影条件を用いる。
規約：族の原像に新しい充填条件を要求しない。
使われ方：HTT 4.2.4.1 の逆対応を元の切断空間へ持ち上げる条件。 -/
lemma uliftSectionsFamilyDown_projection (p : E ⟶ K) (A : SSet.{u})
    (g : (SSet.uliftFunctor.{v, u}).obj A ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections ((SSet.uliftFunctor.{v, u}).map p)) :
    uliftSectionsFamilyDown p A g ≫ p = fst K A := by
  apply (SSet.uliftFunctor.{v, u}).map_injective
  dsimp only [uliftSectionsFamilyDown]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_preimage]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation_projection, whiskerLeft_fst]
  rfl

/-- 概要：持ち上げたパラメータからの切断を元のパラメータからの切断へ戻す。
方針：元の宇宙へ戻した評価の族を切断空間へ持ち上げる。
規約：順方向の比較と同じ普遍的な切断模型を使う。
使われ方：HTT 4.2.4.1 の切断比較の逆対応。 -/
noncomputable def uliftSectionsHomDown (p : E ⟶ K) (A : SSet.{u})
    (g : (SSet.uliftFunctor.{v, u}).obj A ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections ((SSet.uliftFunctor.{v, u}).map p)) : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift (uliftSectionsFamilyDown p A g) (uliftSectionsFamilyDown_projection p A g)

/-- 概要：元へ戻した切断を評価すると元へ戻した評価の族になる。
方針：切断空間への持ち上げの評価の式を使う。
規約：パラメータは元の A。
使われ方：HTT 4.2.4.1 の逆対応の両方向の計算。 -/
lemma uliftSectionsHomDown_evaluation (p : E ⟶ K) (A : SSet.{u})
    (g : (SSet.uliftFunctor.{v, u}).obj A ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections ((SSet.uliftFunctor.{v, u}).map p)) :
    (K ◁ uliftSectionsHomDown p A g) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation p =
      uliftSectionsFamilyDown p A g := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift_evaluation _ _

/-- 概要：小さいパラメータの切断とその持ち上げのパラメータの切断は全単射に対応する。
方針：普遍的な評価と ULift の完全忠実性で両逆関係を示す。
規約：順方向は標準比較射への後合成のまま。
使われ方：HTT 4.2.4.1 の切断空間の ULift 比較が同型であることの検証。 -/
noncomputable def uliftSectionsHomEquiv (p : E ⟶ K) (A : SSet.{u}) :
    (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p) ≃
      ((SSet.uliftFunctor.{v, u}).obj A ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections ((SSet.uliftFunctor.{v, u}).map p)) where
  toFun f := (SSet.uliftFunctor.{v, u}).map f ≫ uliftSectionsComparison p
  invFun := uliftSectionsHomDown p A
  left_inv f := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections_hom_ext
    apply (SSet.uliftFunctor.{v, u}).map_injective
    rw [uliftSectionsHomDown_evaluation]
    dsimp only [uliftSectionsFamilyDown]
    rw [CategoryTheory.Functor.map_preimage,
      uliftSectionsComparison_map_evaluation, Iso.hom_inv_id_assoc]
  right_inv g := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections_hom_ext
    rw [uliftSectionsComparison_map_evaluation, uliftSectionsHomDown_evaluation]
    dsimp only [uliftSectionsFamilyDown]
    rw [CategoryTheory.Functor.map_preimage, Iso.inv_hom_id_assoc]


/-- 概要：切断空間の ULift と持ち上げた射影の切断空間の各次数は全単射。
方針：標準単体の Yoneda 表示とパラメータの切断の全単射を合成する。
規約：標準単体の宇宙も同時に移す。
使われ方：HTT 4.2.4.1 の標準切断比較が厳密な同型であることの検証。 -/
noncomputable def uliftSectionsSimplexEquiv (p : E ⟶ K) (n : ℕ) :
    ((SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p)) _⦋n⦌ ≃
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections ((SSet.uliftFunctor.{v, u}).map p)) _⦋n⦌ :=
  Equiv.ulift.trans (SSet.yonedaEquiv.symm.trans
    ((uliftSectionsHomEquiv p Δ[n]).trans
      (((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso n).homCongr (Iso.refl _)).trans SSet.yonedaEquiv)))

/-- 概要：各次数の全単射の順方向は構成済みの標準切断比較の成分。
方針：同型で移した Yoneda 射の式と後合成の自然性を使う。
規約：全単射の選択で比較射を変えない。
使われ方：HTT 4.2.4.1 の実際の切断比較の同型性。 -/
lemma uliftSectionsSimplexEquiv_apply (p : E ⟶ K) {n : ℕ}
    (s : ((SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p)) _⦋n⦌) :
    uliftSectionsSimplexEquiv p n s =
      (uliftSectionsComparison p).app (Opposite.op ⦋n⦌) s := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso n).inv ≫
    (((SSet.uliftFunctor.{v, u}).map (SSet.yonedaEquiv.symm s.down) ≫
      uliftSectionsComparison p) ≫ 𝟙 _)) = _
  rw [Category.comp_id, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftYonedaMap,
    SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  cases s
  rfl

/-- 概要：切断空間の ULift の標準比較射は厳密な同型。
方針：各次数の成分が全単射であることを既存の全単射から移す。
規約：任意の射 p に適用し、Kan 性や fibration 性は不要。
使われ方：HTT 4.2.4.1 の重み付き end の持ち上げと切断模型の同定。 -/
instance uliftSectionsComparison_isIso (p : E ⟶ K) : IsIso (uliftSectionsComparison.{u, v} p) := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨⟨n⟩⟩
  rw [isIso_iff_bijective]
  change Function.Bijective (fun s ↦ (uliftSectionsComparison p).app (Opposite.op ⦋n⦌) s)
  have he : (fun s ↦ (uliftSectionsComparison p).app (Opposite.op ⦋n⦌) s) =
      uliftSectionsSimplexEquiv p n :=
    funext (fun s ↦ (uliftSectionsSimplexEquiv_apply p s).symm)
  rw [he]
  exact (uliftSectionsSimplexEquiv p n).bijective

/-- 概要：切断空間の ULift は持ち上げた射影の切断空間と厳密に同型。
方針：構成済みの標準比較射の同型性から逆射を得る。
規約：同型の順方向は標準の比較射。
使われ方：HTT 4.2.4.1 の反転豊穣係数の end を coherent な錐へ接続する。 -/
noncomputable def uliftSectionsIso (p : E ⟶ K) :
    (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p) ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections ((SSet.uliftFunctor.{v, u}).map p) :=
  asIso (uliftSectionsComparison p)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
