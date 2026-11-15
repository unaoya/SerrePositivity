-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Arc.ExcisionDerived（仮。原典 Cor 8.12 と E3 の欄 excision）
-- 設計書：formalization-plans/bhatt-scholze/a6-design.md §2.3・§3.2 の 5・6、単位 A6-4。基準コミット efa846fe8。型検査対象（5∞-0）。
module

public import SerrePositivity.EInfinity.Perfectoidization.TheoryInterface
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Definition
-- 本ファイルは drafts/A6/{SheafOfSetsExcision,ArcSheafProperty}.lean、drafts/Sheaves/SpaceValued.lean（S8）、drafts/A4/InterfaceFields.lean、
-- drafts/A5/PerfectSiteComparison.lean を import する。

/-!
# excision（BS 著者版 Cor 8.12）と E3 の欄 `excision`

## 概要
S → S′ 離散で導来 p 完備、I ⊂ S 導来 p 完備（S 加群として）、`ArcOutside f I` ⇒ CAlg_R の四角形 S_perfd → S′_perfd、S_perfd → (S/I)_perfd、
S′_perfd → (S′/IS′)_perfd、(S/I)_perfd → (S′/IS′)_perfd は引き戻し。E3 の欄 `excision` はこれ（界面の `ordinarySquare … ≫ perfd`）。

## 方針
A6-3 の集合の層の押し出し F_S = F_{S′} ⊔_{F_{S′/I}} F_{S/I} を S8 で空間値の層の押し出しに持ち上げ（単射に沿う離散の押し出しは離散、
離散な前層の層化は 1 圏の層化）、前層の押し出し P → F_S が局所同値、E 値の層 O（Prop 8.10）は局所同値で局所的なので
Γ(F_S, O) ≃ Γ(P, O) = Γ(F_{S′}, O) ×_{Γ(F_{S′/I}, O)} Γ(F_{S/I}, O)、Γ(F_T, O) = lim_{Perfd_{T/}} O = T_perfd（Prop 8.5）。

## 規約
S・T は完備なので `e3Perfd_of_complete`（A4-3）で S_perfd に読み替える。S/I は完備（G-A6-10）だが **T/IT は一般に完備でない**（W9-II-15 の反例）ので、
商は `completionRing` 経由の自然同型 F_U ≃ F_{completionRing U}、Γ(F_U, O) ≃ e3Perfd(U) で扱う。CAlg_R の引き戻しは U が反映（G-A5-16）。

## 使われ方
`TheoryPerfectoidizationInterface.excision`（A9）。環の帰結は既存（`Perfectoidization/Derived/Excision`）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.PerfectoidizationInterface SerrePositivity.EInfinity.Perfectoidization
open SerrePositivity.InfinityCategories SerrePositivity.EInfinity SerrePositivity.DerivedCompletion

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)

/-- F_U の元 (P,l : U→P) に、l と R→U の合成を係数射とする P を対応させる。 -/
def elementAlgebras (κ : Cardinal.{u}) (U : A_R R) : (homPresheaf p κ U.right).Elements ⥤ A_R R where
  obj x := Under.mk (CommRingCat.ofHom (x.val.comp U.hom.hom))
  map f := Under.homMk ((arcPerfdRingFunctor p κ).map f.hom) (by
    sorry) -- f.map_val は指定された U→P を保つ。R→U を前合成する
  map_id := by sorry -- 環への忘却で恒等射
  map_comp := by sorry -- 環への忘却で合成

def elementAlgebraNerve (κ : Cardinal.{u}) (U : A_R R) :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (homPresheaf p κ U.right).Elements) ⟶ algebraNerve R where
  app n := ↾fun x => ((elementAlgebras p R κ U).mapComposableArrows _).obj x.down
  naturality := by sorry -- nerve の射列への後合成

abbrev elementStructure (κ : Cardinal.{u}) (U : A_R R) :=
  elementAlgebraNerve p R κ U ≫ E.discrete R

/-- ℤ に沿って制限すると元の圏への O の引き戻しになる。 -/
def elementStructure_forget (κ : Cardinal.{u}) (U : A_R R) :
    let z : ArcZ.{u} →+* R := (Int.castRingHom R).comp ULift.ringEquiv.toRingHom
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (elementStructure (E := E) p R κ U ≫ cAlgRestrictScalars (E := E) z)
      ((SSet.uliftFunctor.{u+1,u}).map (nerveMap (Functor.Elements.π (homPresheaf p κ U.right))) ≫
        structurePresheaf (E := E) p κ) := by
  sorry -- cAlgRestrictScalars_algebraEmbedding で係数を戻すと arcIntegerAlgebras の構造射、
        -- 元の圏の全射について同じ環準同型なので自然

/-- Γ を U に関して関手化する。R-構造を備えた κ 以下の試験環の包含に沿う
右 Kan 拡張の U での図式は (P,l : U→P) 上の elementStructure。 -/
def arcElementSections (κ : Cardinal.{u}) : algebraNerve R ⟶ E.CAlg R :=
  let i := elementAlgebraNerve p R κ (ofAlgebra R R)
  Classical.choose (show ∃ G, ∃ α : SSet.Homotopy (i ≫ G) (i ≫ E.discrete R),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension i (i ≫ E.discrete R) G α from by
    sorry) -- 各 comma 圏は小さい元の圏と同値、CAlg_R での点ごとの極限から取る

/-- 固定した κ で A5 と比較できる始域。必要な有限図式には共通の κ を取る。 -/
abbrev arcInputProperty (κ : Cardinal.{u}) : ObjectProperty (A_R R) := fun U =>
  perfectSiteCutoff p R (completionRing p U.right) ≤ κ

/-- 試験環 P と R→P の組。元の圏に係数を持ち上げるための小さい模型。 -/
abbrev markedTests (κ : Cardinal.{u}) := (homPresheaf p κ R).Elements

def markedAlgebras (κ : Cardinal.{u}) :
    ((markedTests p R κ)ᵒᵖ)ᵒᵖ ⥤ A_R R :=
  unopUnop _ ⋙ elementAlgebras p R κ (ofAlgebra R R)

def markedStructure (κ : Cardinal.{u}) :
    Sheaves.Presheaf (markedTests p R κ)ᵒᵖ (E.CAlg R) :=
  Sheaves.ringPresheafToCAlg (E := E) R (markedAlgebras p R κ)

abbrev markedHom (κ : Cardinal.{u}) (U : A_R R) :=
  markedAlgebras p R κ ⋙ coyoneda.obj (Opposite.op U)

/-- U→P に R→U→P を付ける。R を指定した側では U からの射は R 上の射になる。 -/
def markTarget (κ : Cardinal.{u}) (U : A_R R) :
    (homPresheaf p κ U.right).Elements ⥤ (markedHom p R κ U).Elements where
  obj x := by
    let r := (homPresheaf p κ R).elementsMk x.obj (x.val.comp U.hom.hom)
    exact (markedHom p R κ U).elementsMk (Opposite.op (Opposite.op r))
      (Under.homMk (CommRingCat.ofHom x.val) (by sorry)) -- R の構造射は l との合成
  map {x y} f := by
    let rx := (homPresheaf p κ R).elementsMk x.obj (x.val.comp U.hom.hom)
    let ry := (homPresheaf p κ R).elementsMk y.obj (y.val.comp U.hom.hom)
    let g : rx ⟶ ry := ⟨f.hom, by
      sorry⟩ -- f.map_val の両辺に R→U を前合成
    exact ⟨g.op.op, by
      sorry⟩ -- U 上の等式は f.map_val
  map_id := by sorry -- 元の圏の忘却は忠実
  map_comp := by sorry -- 基礎環の射の合成

def markedTargetEquiv (κ : Cardinal.{u}) (U : A_R R) :
    (homPresheaf p κ U.right).Elements ≌ (markedHom p R κ U).Elements := by
  letI : (markTarget p R κ U).IsEquivalence := by
    sorry -- 逆は R の標識を忘れる。U→P が R 上なので復元した標識は元の標識と等しい
  exact (markTarget p R κ U).asEquivalence

abbrev sectionLimit (κ : Cardinal.{u}) (U : A_R R) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (Sheaves.sectionsOfDiagram (markedHom p R κ U) (markedStructure (E := E) p R κ))

abbrev markedSections (κ : Cardinal.{u}) (U : A_R R) (h : sectionLimit (E := E) p R κ U) :=
  Sheaves.sectionsOf (markedHom p R κ U) (markedStructure (E := E) p R κ) h

/-- 概要：S8 の 6：Γ(F_T, O) := lim_{el(F_T)} O = lim_{Perfd_{T/}} O（F_T の元の圏は Perfd_{T/}）、これは T_perfd（Prop 8.5 の極限の形、A5-1）。
方針：`sectionsOf`（Sheaves/SpaceValued）と `perfectoidization_isLimit`。
規約：CAlg_R。
使われ方：`perfectoidization_excision`。 -/
def sectionsOf_homSheaf_eq_perfectoidization (κ : Cardinal.{u})
    [Fact ((κ + Cardinal.aleph0) ^ Cardinal.aleph0 ≤ κ)]
    (T : Type u) [CommRing T] [Algebra R T]
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hb : perfectSiteCutoff p R T ≤ κ) (h : sectionLimit (E := E) p R κ (ofAlgebra R T)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (markedSections (E := E) p R κ (ofAlgebra R T) h) (perfectoidization (E := E) p R hR T hT) := by
  let U := ofAlgebra R T
  let F := markedHom p R κ U
  let O := markedStructure (E := E) p R κ
  let e := markedTargetEquiv p R κ U
  let Γ := perfectoidization_isLimit (E := E) p R hR T hT
  let c := Γ.choose
  let D := (SSet.uliftFunctor.{u+1,u}).map (nerveMap (e.functor ⋙ Functor.Elements.π F)) ≫ O
  have hc : ∃ t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone D, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone t ∧ t.vertex = c.vertex := by
    sorry -- c は A5 の κ₀ 極限錐。共通の弱始対象と Čech 余積は κ₀≤κ に入り、
          -- 両錐の脚は R→T→P に沿う同じ射。D47 で c.vertex に極限錐を移す
  exact Sheaves.sectionsOf_eq_limit_elements F O h e hc.choose hc.choose_spec.1 ≪≫
    eqToIso (congrArg HomotopyCategory.mk (hc.choose_spec.2.trans Γ.choose_spec.2))

/-- まず集合の前層の圏で押し出す。P の構造射を保ったまま S8 に渡す。 -/
abbrev homPushoutPresheaf (κ : Cardinal.{u}) [Fact ((κ + Cardinal.aleph0) ^ Cardinal.aleph0 ≤ κ)]
    {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :=
  Sheaves.presheafPushout
    (homSheafMap p κ (quotientProjection R T (I.map f.right.hom)).right).hom
    (homSheafMap p κ (quotientComparison R f I).right).hom

def homPushoutComparison (κ : Cardinal.{u}) [Fact ((κ + Cardinal.aleph0) ^ Cardinal.aleph0 ≤ κ)]
    {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :
    homPushoutPresheaf p R κ f I ⟶ homPresheaf p κ S.right :=
  CategoryTheory.Limits.pushout.desc (homSheafMap p κ f.right).hom
    (homSheafMap p κ (quotientProjection R S I).right).hom (by
      sorry) -- 各試験環で quotientSquare_commutes に沿って前合成

theorem homPushoutComparison_sheafify (κ : Cardinal.{u}) [Fact ((κ + Cardinal.aleph0) ^ Cardinal.aleph0 ≤ κ)]
    {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right)
    (hS : IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right S.right))
    (hT : IsModuleComplete T.right (p : T.right) (ModuleCat.of T.right T.right))
    (hI : IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right I))
    (h : ArcOutside R p f I) (b : ExcisionBounds p R κ f I) :
    IsIso ((presheafToSheaf (arcTopologyPerfd p κ) (Type u)).map (homPushoutComparison p R κ f I)) := by
  sorry -- presheafToSheaf は左随伴。三つの Hom は既に層なので homSheaf_pushout の比較射になる

/-- affCompl 上で Hom(U,−) を表す対象は H⁰ 完備化。全四隅を同じ κ で取る。 -/
def complHomMap (κ : Cardinal.{u}) {U V : CommRingCat.{u}} (f : U ⟶ V)
    (hu : Cardinal.mk (completionRing p U) ≤ κ) (hv : Cardinal.mk (completionRing p V) ≤ κ) :=
  yoneda.map (completedArcMap p κ f hu hv).op

def complPushoutComparison (κ : Cardinal.{u}) {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right)
    (b : ExcisionBounds p R κ f I) :
    Sheaves.presheafPushout
      (complHomMap p κ (quotientProjection R T (I.map f.right.hom)).right b.target b.targetQuot)
      (complHomMap p κ (quotientComparison R f I).right b.sourceQuot b.targetQuot) ⟶
      yoneda.obj (Opposite.op (completedArcObj p κ S.right b.source)) :=
  Limits.pushout.desc (complHomMap p κ f.right b.source b.target)
    (complHomMap p κ (quotientProjection R S I).right b.source b.sourceQuot) (by
      sorry) -- 商の可換四角形を完備化し、Yoneda で送る

/-- 概要：前層の押し出し P := F_{S′} ⊔_{F_{S′/I}} F_{S/I}（点ごとの集合の押し出し、離散）から F_S への射は arc 局所同値（S8 の 2・3 と A6-3 の `homSheaf_pushout`）。
方針：`discretePushout_isDiscrete`、`sheafify_discrete_eq`、`localEquiv_of_sheafifyIso`。
規約：—
使われ方：`perfectoidization_excision`。 -/
theorem homPresheafPushout_localEquiv (κ : Cardinal.{u}) [Fact ((κ + Cardinal.aleph0) ^ Cardinal.aleph0 ≤ κ)]
    {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right)
    (hS : IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right S.right))
    (hT : IsModuleComplete T.right (p : T.right) (ModuleCat.of T.right T.right))
    (hI : IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right I))
    (h : ArcOutside R p f I) (b : ExcisionBounds p R κ f I) :
    Sheaves.IsLocalEquivSet (arcTopology p κ) (complPushoutComparison p R κ f I b) ∧
      Sheaves.IsLocalEquivSet (arcTopologyPerfd p κ) (homPushoutComparison p R κ f I) := by
  constructor
  · sorry -- 層化の随伴と Yoneda。全ての集合の arc 層への Hom は sheafOfSets_excision の引き戻し
  · exact homPushoutComparison_sheafify p R κ f I hS hT hI h b

/-- Prop 8.10 の O に対する S8-5。辺の向きは Γ(F_S,O) → Γ(P,O)。 -/
theorem sections_homPushout_invertible (κ : Cardinal.{u}) [Fact ((κ + Cardinal.aleph0) ^ Cardinal.aleph0 ≤ κ)]
    {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right)
    (hφ : Sheaves.IsLocalEquivSet (arcTopologyPerfd p κ) (homPushoutComparison p R κ f I))
    (hP : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (Sheaves.sectionsOfDiagram (homPushoutPresheaf p R κ f I) (structurePresheaf (E := E) p κ)))
    (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (Sheaves.sectionsOfDiagram (homPresheaf p κ S.right) (structurePresheaf (E := E) p κ))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (Sheaves.sectionsOf_map (homPushoutComparison p R κ f I) (structurePresheaf (E := E) p κ) hP hS).toTruncated := by
  exact Sheaves.sections_localEquiv_iso (arcTopologyPerfd p κ) _ hφ _ (structurePresheaf_isArcSheaf (E := E) p κ) hP hS

/-- 概要：G-A6-10：S・I が導来 p 完備なら S/I も（cofiber）。**T/IT については成り立たない**（W9-II-15：S = R ⊕ c₀(R)、T = R⟨t⟩ ⊕ c₀(R⟨t⟩)、I = 0 ⊕ c₀(R) で
S・T・I 完備かつ `ArcOutside` だが T/IT の直和因子が非零で p 可除）。旧「T と IT についても」は撤回。
方針：完備加群の短完全列（HA/DerivedCompletion、2b 後の名前）。
規約：—
使われ方：`e3Excision` で S/I を Def 8.2 の定義域に入れる。 -/
theorem quotient_isModuleComplete (S : Type u) [CommRing S] (I : Ideal S)
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hI : IsModuleComplete S (p : S) (ModuleCat.of S I)) :
    IsModuleComplete (S ⧸ I) (p : S ⧸ I) (ModuleCat.of (S ⧸ I) (S ⧸ I)) := by
  sorry -- 0→I→S→S/I→0 の cofiber は D(S) の p 完備部分圏にあり、係数制限で完備性を反映

/-- 概要：一般の離散 R 代数 U について、Perfd 上の前層 F_U = Hom(U, −) ≃ F_{completionRing U}（perfectoid 標的は p 完備、`completionRing` の普遍性 Interface.lean:237）、
よって Γ(F_U, O) ≃ Γ(F_{completionRing U}, O) ≃ (completionRing U)_perfd = e3Perfd(U)（Prop 8.5 の Type u 版、D41）。U について自然（商写像・比較写像を含む四角形を
自然変換として移す）。
方針：W9-II-15 の修復。T → completionRing(T/IT) の全射性は要らない（F_{T/IT} ↪ F_T の単射性は T → T/IT の全射性から）。
規約：affCompl_κ の対象として商を使う箇所は completionRing(T/IT)。
使われ方：`e3Excision`。 -/
def homPresheaf_completionRing_iso (κ : Cardinal.{u}) [Fact ((κ + Cardinal.aleph0) ^ Cardinal.aleph0 ≤ κ)] :
    (ringCompletionFunctor p).op ⋙ homSheafFunctor p κ ≅ homSheafFunctor p κ :=
  NatIso.ofComponents (fun U => by
    let η := homSheafMap p κ (completionUnit p U.unop)
    have hη : IsIso η := by
      sorry -- 各 perfectoid 試験環は p 完備、各成分の逆は completionLift、completion_existsUnique
    exact @asIso _ _ _ _ η hη) (by
      sorry) -- completionMap_comp から商射を含むすべての射で自然

/-- 同一の κ で覆う離散入力に制限した Γ の自然比較。 -/
def sectionsFunctorIsoE3 (κ : Cardinal.{u}) [Fact ((κ + Cardinal.aleph0) ^ Cardinal.aleph0 ≤ κ)] :
    let i := nerveMap (arcInputProperty p R κ).ι
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (i ≫ arcElementSections (E := E) p R κ) (i ≫ e3Perfd (E := E) p R hR) := by
  sorry -- 右 Kan 拡張の脚は U→P。homPresheaf_completionRing_iso の単位は U に自然なので、
        -- 完備化後の Prop 8.5 の比較錐が四角形の全射・二単体について可換

def sectionsOf_homSheaf_eq_e3Perfd (κ : Cardinal.{u}) [Fact ((κ + Cardinal.aleph0) ^ Cardinal.aleph0 ≤ κ)]
    (U : (arcInputProperty p R κ).FullSubcategory) (h : sectionLimit (E := E) p R κ U.obj) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (markedSections (E := E) p R κ U.obj h) ((e3Perfd (E := E) p R hR).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U.obj)) := by
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (markedSections (E := E) p R κ U.obj h) ((arcElementSections (E := E) p R κ).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U.obj)) := by
    sorry -- markedTargetEquiv で sectionsOf の極限を同じ U→P の右 Kan 拡張の値に比較
  exact e ≪≫ (sectionsFunctorIsoE3 (E := E) p R hR κ).app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U)

/-- R の構造射を忘れた切断は global な O の切断である。 -/
def sections_forget_to_integers (κ : Cardinal.{u}) (U : A_R R)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (Sheaves.sectionsOfDiagram (homPresheaf p κ U.right) (structurePresheaf (E := E) p κ))) :
    let z : ArcZ.{u} →+* R := (Int.castRingHom R).comp ULift.ringEquiv.toRingHom
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((arcElementSections (E := E) p R κ ≫ cAlgRestrictScalars (E := E) z).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U))
      (Sheaves.sectionsOf (homPresheaf p κ U.right) (structurePresheaf (E := E) p κ) h) := by
  sorry -- elementStructure_forget は全脚を保つ。係数制限は右随伴なので元の圏の極限を保ち、
        -- 右 Kan 拡張の評価錐を sectionsOfCone に比較できる

/-- Γ(F_S,O) は Γ(F_T,O) → Γ(F_{T/IT},O) ← Γ(F_{S/I},O) の引き戻し。
四辺と二単体は環の商の四角形そのものの像。 -/
theorem sections_excision_square (κ : Cardinal.{u}) [Fact ((κ + Cardinal.aleph0) ^ Cardinal.aleph0 ≤ κ)]
    {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right)
    (hS : IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right S.right))
    (hT : IsModuleComplete T.right (p : T.right) (ModuleCat.of T.right T.right))
    (hI : IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right I))
    (h : ArcOutside R p f I) (b : ExcisionBounds p R κ f I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (quotientExcisionSquare R f I ≫ arcElementSections (E := E) p R κ) := by
  have hφ := (homPresheafPushout_localEquiv p R κ f I hS hT hI h b).2
  sorry -- sections_homPushout_invertible に hφ を渡し、Γ(F_S,O) を Γ(P,O) に移す。
        -- 商射の脚は Mono。sectionsOf_pushout（引き戻しの述語）待ち。
        -- sections_forget_to_integers の脚は環の射に自然で、係数制限は極限を反映する

/-- 概要：Cor 8.12：四角形 S_perfd、S′_perfd、(S/I)_perfd、(S′/IS′)_perfd は CAlg_R の引き戻し（S′ は与えられたもの）。
方針：`excision_of_excision_prod`（A6-3）で S′ × S/I に替え、`homPresheafPushout_localEquiv` と S8 の 5（`sections_localEquiv_iso`、O は層：`structurePresheaf_isArcSheaf`）、
S8 の 4（Γ(−, O) は前層の押し出しを引き戻しに）、`sectionsOf_homSheaf_eq_perfectoidization`。引き戻しの射が perfd の関手性の射に一致すること（紙 4）。
規約：D(R) で示し U が反映（G-A5-16）。
使われ方：`e3Excision`。 -/
theorem perfectoidization_excision {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right)
    (hS : IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right S.right))
    (hT : IsModuleComplete T.right (p : T.right) (ModuleCat.of T.right T.right))
    (hI : IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right I))
    (h : ArcOutside R p f I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (quotientExcisionSquare R f I ≫ e3Perfd (E := E) p R hR) := by
  sorry -- 四隅の完備化・A_inf(R) を含む κ で sections_excision_square を使う。
        -- sectionsOf_pushout（引き戻しの述語）待ち。sectionsFunctorIsoE3 を商の四角形に
        -- 前合成し、Γ の極限錐を e3Perfd の指定四辺・二単体へまとめて移す

/-- 概要：E3 の `excision`：`IsPullbackSquare (ordinarySquare R f (quotientProjection R S I) (quotientProjection R T (I.map f.right.hom)) (quotientComparison R f I) (quotientSquare_commutes R f I) ≫ e3Perfd p R)`。
方針：`perfectoidization_excision` を S・T（完備、`e3Perfd_of_complete`）と S/I（完備、`quotient_isModuleComplete`）に、T/IT は
`homPresheaf_completionRing_iso`・`sectionsOf_homSheaf_eq_e3Perfd` で completionRing(T/IT) 経由に読み替え、四角形を自然変換として移す（W9-II-15）。
規約：`TheoryPerfectoidizationInterface.excision` の型そのまま。
使われ方：A9。 -/
theorem e3Excision {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right)
    (hS : IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right S.right))
    (hT : IsModuleComplete T.right (p : T.right) (ModuleCat.of T.right T.right))
    (hI : IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right I))
    (h : ArcOutside R p f I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (ordinarySquare R f (quotientProjection R S I)
      (quotientProjection R T (I.map f.right.hom)) (quotientComparison R f I)
      (quotientSquare_commutes R f I) ≫ e3Perfd (E := E) p R hR) :=
  perfectoidization_excision (E := E) p R hR f I hS hT hI h

end SerrePositivity.BhattScholze.Perfectoidization.Derived
