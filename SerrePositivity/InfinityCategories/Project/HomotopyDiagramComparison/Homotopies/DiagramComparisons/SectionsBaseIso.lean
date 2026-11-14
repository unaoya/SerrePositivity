module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeSections

/-!
概要：底の単体集合の厳密な同型に沿って切断空間を同型で移す。
方針：普遍的な切断の族を底の逆同型で前合成し、評価の一意性で往復則を示す。
規約：全空間の射は変えず、射影の後で底の同型を合成する。
使われ方：HTT 4.2.4.1 の宇宙を調整した nerve 上の切断比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet MonoidalCategory CartesianMonoidalCategory
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

variable {K L E E' : SSet.{u}}

/-- 概要：底の同型の逆で切断の族を前合成して新しい底の切断にする。
方針：底の固定条件を同型の往復則で確認して切断空間へ持ち上げる。
規約：射影 p の終域 K を同型 e : K≅L で移す。
使われ方：HTT 4.2.4.1 の切断比較の底の変更。 -/
noncomputable def simplicialSectionsBaseMap (p : E ⟶ K) (e : K ≅ L) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (p ≫ e.hom) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift ((e.inv ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation p) (by
    rw [Category.assoc, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation p) p e.hom,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation_projection, whiskerRight_fst_assoc,
      e.inv_hom_id, Category.comp_id])

/-- 概要：底を同型で移した切断を元の底へ戻す。
方針：元の底からの同型で前合成し、終域の同型を消去して固定条件を示す。
規約：射影の合成を定義的に元と同一視せず、同型の単射性を使う。
使われ方：HTT 4.2.4.1 の底の切断空間の同型の逆射。 -/
noncomputable def simplicialSectionsBaseInv (p : E ⟶ K) (e : K ≅ L) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (p ≫ e.hom) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift
    ((e.hom ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (p ≫ e.hom)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (p ≫ e.hom)) (by
      apply (cancel_mono e.hom).1
      change (e.hom ▷ _) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (p ≫ e.hom) ≫ (p ≫ e.hom)) = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation_projection, whiskerRight_fst])

/-- 概要：底を移す切断写像の評価は逆同型での前合成。
方針：切断空間への持ち上げの評価の式を使う。
規約：新しい底 L を第一因子に置く。
使われ方：HTT 4.2.4.1 の底の変更の往復則と自然性。 -/
@[reassoc]
lemma simplicialSectionsBaseMap_evaluation (p : E ⟶ K) (e : K ≅ L) :
    (L ◁ simplicialSectionsBaseMap p e) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (p ≫ e.hom) =
      (e.inv ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift_evaluation _ _

/-- 概要：底を戻す切断写像の評価は順方向の同型での前合成。
方針：切断空間への持ち上げの評価の式を使う。
規約：元の底 K を第一因子に置く。
使われ方：HTT 4.2.4.1 の底の変更の往復則。 -/
lemma simplicialSectionsBaseInv_evaluation (p : E ⟶ K) (e : K ≅ L) :
    (K ◁ simplicialSectionsBaseInv p e) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation p =
      (e.hom ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (p ≫ e.hom)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (p ≫ e.hom) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift_evaluation _ _

/-- 概要：底を移して戻すと切断空間の恒等写像。
方針：普遍的な評価で検出し、二因子の自然性と同型の往復則を使う。
規約：全空間は固定する。
使われ方：HTT 4.2.4.1 の底の変更の厳密な同型。 -/
lemma simplicialSectionsBaseMap_inv (p : E ⟶ K) (e : K ≅ L) :
    simplicialSectionsBaseMap p e ≫ simplicialSectionsBaseInv p e = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections_hom_ext
  rw [whiskerLeft_comp, Category.assoc, simplicialSectionsBaseInv_evaluation,
    whisker_exchange_assoc, simplicialSectionsBaseMap_evaluation]
  simp only [← Category.assoc, ← comp_whiskerRight, e.hom_inv_id,
    id_whiskerRight, Category.id_comp, whiskerLeft_id]

/-- 概要：底を戻してから移しても切断空間の恒等写像。
方針：評価の一意性で二因子の自然性と同型の逆の往復則を使う。
規約：新しい射影は p≫e.hom。
使われ方：HTT 4.2.4.1 の底の変更の厳密な同型の逆則。 -/
lemma simplicialSectionsBaseInv_map (p : E ⟶ K) (e : K ≅ L) :
    simplicialSectionsBaseInv p e ≫ simplicialSectionsBaseMap p e = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections_hom_ext
  rw [whiskerLeft_comp, Category.assoc, simplicialSectionsBaseMap_evaluation,
    whisker_exchange_assoc, simplicialSectionsBaseInv_evaluation]
  simp only [← Category.assoc, ← comp_whiskerRight, e.inv_hom_id,
    id_whiskerRight, Category.id_comp, whiskerLeft_id]

/-- 概要：底の厳密な同型は切断空間の厳密な同型を誘導する。
方針：構成した二射と両方の往復則をまとめる。
規約：Kan 性や fibration 性を仮定しない。
使われ方：HTT 4.2.4.1 の持ち上げた nerve から標準の添字圏への切断の移送。 -/
noncomputable def simplicialSectionsBaseIso (p : E ⟶ K) (e : K ≅ L) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (p ≫ e.hom) where
  hom := simplicialSectionsBaseMap p e
  inv := simplicialSectionsBaseInv p e
  hom_inv_id := simplicialSectionsBaseMap_inv p e
  inv_hom_id := simplicialSectionsBaseInv_map p e

/-- 概要：切断空間の底の変更は全空間の底を保つ射に自然。
方針：新しい底で評価し、後合成と第一因子の前合成を交換する。
規約：可換条件の証明を明示し、同型による底の変更を両射影に同時に行う。
使われ方：HTT 4.2.4.1 の具体的な切断比較の同値性を底の同型で移す。 -/
lemma simplicialSectionsBaseMap_naturality (p : E ⟶ K) (q : E' ⟶ K) (e : K ≅ L)
    (f : E ⟶ E') (hf : f ≫ q = p) :
    simplicialSectionsBaseMap p e ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f (by rw [← Category.assoc, hf]) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f hf ≫ simplicialSectionsBaseMap q e := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections_hom_ext
  simp only [whiskerLeft_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap_evaluation,
    simplicialSectionsBaseMap_evaluation_assoc, simplicialSectionsBaseMap_evaluation,
    whisker_exchange_assoc]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
