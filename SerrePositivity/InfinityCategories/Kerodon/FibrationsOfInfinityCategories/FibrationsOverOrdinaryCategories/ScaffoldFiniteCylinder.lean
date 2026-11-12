module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiniteExtension
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.F1DiagramsTrianglePrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence

/-!
概要：有限鎖の拡張の始域を最初の係数と尾部の写像円柱として表示する。
方針：辺と尾部の nerve の pushout に係数との積を取り、尾部の組み立て射と貼る。
規約：円柱の貼り合わせ端点は時刻一であり、係数の充填性は不要。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、scaffold の比較を区間の場合へ帰着する段階。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：組み立て射を指定頂点に制限すると係数変換と定値包含の合成になる。
方針：底の射列を定値に評価し、係数の Yoneda 表示の自然性を使う。
規約：底の圏の他の対象や射には制限を課さない。
使われ方：Kerodon Remark 5.3.2.12（Tag 0252）、Theorem 5.3.5.7（Tag 037Q）、円柱の終点の計算。 -/
lemma simplicialReplacementAssembly_nervePoint
    {C : Type u} [Category.{u} C] {K : SSet.{u}} {F : C ⥤ SSet.{u}}
    (η : (CategoryTheory.Functor.const C).obj K ⟶ F) (c : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementAssembly η =
      snd (Δ[0] : SSet.{u}) K ≫ η.app c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift F c := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, s⟩
  refine Sigma.ext (by rfl) ?_
  exact heq_of_eq (SSet.yonedaEquiv_symm_comp s (η.app c))

/-- 概要：最初の係数値から尾部の replacement の最初の fiber への射。
方針：最初の構造射を適用した後、尾部の定値射列として含める。
規約：全体の頂点一は尾部の頂点零に対応する。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、写像円柱の貼り合わせ射。 -/
noncomputable def scaffoldFiniteCylinderAttachingMap (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    F.obj (ULift.up 0) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n ⋙ F) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialCoefficient F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 1))).app
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n).obj (ULift.up 0)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n ⋙ F) (ULift.up 0)

/-- 概要：最初の係数の prism を有限鎖の拡張の始域へ含める射。
方針：辺と尾部の pushout の左包含と、尾部の replacement を貼る左包含を合成する。
規約：prism の時刻は標準区間の向きと一致する。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、写像円柱表示の円柱部分。 -/
noncomputable def scaffoldFiniteCylinderPrism (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ F.obj (ULift.up 0) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteExtension n F :=
  (pushout.inl (stdSimplex.δ (0 : Fin 2))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _)) ▷ F.obj (ULift.up 0)) ≫
    pushout.inl _ _

/-- 概要：尾部の replacement を有限鎖の拡張の始域へ含める射。
方針：定義の pushout の右包含を使う。
規約：係数の構造射は変更しない。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、写像円柱表示の終域部分。 -/
noncomputable def scaffoldFiniteCylinderTail (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n ⋙ F) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteExtension n F :=
  pushout.inr _ _

/-- 概要：有限鎖の拡張の始域は最初の係数から尾部への射の写像円柱。
方針：二つの pushout を縦に貼り、零単体と係数の積を係数値へ同型で移す。
規約：貼る端点は prismEndpoint 1。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、Theorem 5.2.4.1（Tag 024N） の区間上の比較の適用。 -/
lemma scaffoldFiniteCylinder_isPushout (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldFiniteCylinderAttachingMap n F)
      (scaffoldFiniteCylinderPrism n F) (scaffoldFiniteCylinderTail n F) := by
  let K := F.obj (ULift.up 0)
  let v := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _)
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementAssembly (CategoryTheory.Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialCoefficient F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 1))))
  have ht := (IsPushout.of_hasPushout (stdSimplex.δ (0 : Fin 2)) v).map (tensorRight K)
  have hb := IsPushout.of_hasPushout (pushout.inr (stdSimplex.δ (0 : Fin 2)) v ▷ K) b
  have hp := ht.paste_vert hb
  apply hp.of_iso (asIso (snd (Δ[0] : SSet.{u}) K))
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · change (stdSimplex.δ (0 : Fin 2) ▷ K) ≫ 𝟙 _ =
      snd Δ[0] K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K
    rw [Category.comp_id]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.trianglePrism_endpoint_one K
  · change (v ▷ K) ≫ b ≫ 𝟙 _ = snd Δ[0] K ≫ scaffoldFiniteCylinderAttachingMap n F
    rw [Category.comp_id]
    exact simplicialReplacementAssembly_nervePoint _ _
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl

/-- 概要：有限鎖の拡張と標準の写像円柱との厳密な同型。
方針：構成した pushout の一意性を使う。
規約：通常の単体集合の同型であり、全空間の同値判定とは分ける。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、最初の係数から尾部への写像円柱の表示。 -/
noncomputable def scaffoldFiniteCylinderIso (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteExtension n F ≅
      pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldFiniteCylinderAttachingMap n F) :=
  (scaffoldFiniteCylinder_isPushout n F).isoPushout

/-- 概要：標準の写像円柱から有限鎖の全 replacement への比較射。
方針：円柱表示の逆同型を既存の拡張射に前置する。
規約：貼り合わせ射の終域は尾部の全 replacement。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、小さい円柱部分と全体の比較。 -/
noncomputable def scaffoldFiniteCylinderComparison (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldFiniteCylinderAttachingMap n F) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F :=
  (scaffoldFiniteCylinderIso n F).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteExtensionMap n F

/-- 概要：標準の写像円柱から全 replacement への比較は inner anodyne。
方針：既存の拡張射の性質を始域の同型で移す。
規約：係数の Kan 性を仮定しない。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、帰納段階の inner anodyne な比較。 -/
lemma scaffoldFiniteCylinderComparison_innerAnodyne (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    innerAnodyneExtensions (scaffoldFiniteCylinderComparison n F) := by
  rw [scaffoldFiniteCylinderComparison, innerAnodyneExtensions.cancel_left_of_respectsIso]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteExtensionMap_innerAnodyne n F

/-- 概要：写像円柱の比較を区間部分に制限すると最初の辺の組み立て射になる。
方針：pushout 同型と拡張射の計算則を使い、最初の辺の同定を代入する。
規約：標準区間から二頂点の nerve への標準同型を前置する。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、scaffold の最初の辺上の比較。 -/
lemma scaffoldFiniteCylinderComparison_inl (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldFiniteCylinderAttachingMap n F) ≫
      scaffoldFiniteCylinderComparison n F =
        (((stdSimplex.isoNerve 1).hom ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteFirstEdge n)) ▷ F.obj (ULift.up 0)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialAssembly F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 1)) := by
  rw [scaffoldFiniteCylinderComparison, scaffoldFiniteCylinderIso, ← Category.assoc,
    (scaffoldFiniteCylinder_isPushout n F).inl_isoPushout_inv]
  rw [scaffoldFiniteCylinderPrism, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteExtensionMap, pushout.inl_desc,
    ← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge_inl]

/-- 概要：写像円柱の比較を尾部に制限すると尾部の標準包含になる。
方針：pushout 同型と拡張射の右包含の計算則を使う。
規約：尾部の係数単体を保ったまま底を含める。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、尾部の帰納仮定との接続。 -/
lemma scaffoldFiniteCylinderComparison_inr (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldFiniteCylinderAttachingMap n F) ≫
      scaffoldFiniteCylinderComparison n F = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementBaseMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n) F := by
  rw [scaffoldFiniteCylinderComparison, scaffoldFiniteCylinderIso, ← Category.assoc,
    (scaffoldFiniteCylinder_isPushout n F).inr_isoPushout_inv]
  exact pushout.inr_desc _ _ _

/-- 概要：写像円柱の比較による任意の quasicategory への前合成は同値。
方針：inner anodyne な射の一般的な前合成の定理を使う。
規約：始域と標的自体の quasicategory 性は要求しない。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、写像円柱上の比較から全体の比較への移行。 -/
lemma isPrecompositionEquivalence_scaffoldFiniteCylinderComparison (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (scaffoldFiniteCylinderComparison n F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_innerAnodyne _
    (scaffoldFiniteCylinderComparison_innerAnodyne n F)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
