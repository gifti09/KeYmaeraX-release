package edu.cmu.cs.ls.keymaerax.hydra
// AUTO-GENERATED Slick data model
/** Stand-alone Slick data model for immediate use */
object Tables extends {
  val profile = scala.slick.driver.SQLiteDriver
} with Tables

/** Slick data model trait for extension, choice of backend or usage in the cake pattern. (Make sure to initialize this late.) */
trait Tables {
  val profile: scala.slick.driver.JdbcProfile
  import profile.simple._
  import scala.slick.model.ForeignKeyAction
  // NOTE: GetResult mappers for plain SQL are only generated for tables where Slick knows how to map the types of all columns.
  import scala.slick.jdbc.{GetResult => GR}
  
  /** DDL for all tables. Call .create to execute. */
  lazy val ddl = Agendaitems.ddl ++ Config.ddl ++ Executables.ddl ++ Executionsteps.ddl ++ Lemmas.ddl ++ Models.ddl ++ Proofs.ddl ++ Tacticexecutions.ddl ++ Users.ddl
  
  /** Entity class storing rows of table Agendaitems
   *  @param _Id Database column _id DBType(INTEGER), PrimaryKey
   *  @param proofid Database column proofId DBType(INTEGER)
   *  @param initialproofnode Database column initialProofNode DBType(INTEGER)
   *  @param displayname Database column displayName DBType(STRING) */
  case class AgendaitemsRow(_Id: Option[Int], proofid: Option[Int], initialproofnode: Option[Int], displayname: Option[String])
  /** GetResult implicit for fetching AgendaitemsRow objects using plain SQL queries */
  implicit def GetResultAgendaitemsRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[AgendaitemsRow] = GR{
    prs => import prs._
    AgendaitemsRow.tupled((<<?[Int], <<?[Int], <<?[Int], <<?[String]))
  }
  /** Table description of table agendaItems. Objects of this class serve as prototypes for rows in queries. */
  class Agendaitems(_tableTag: Tag) extends Table[AgendaitemsRow](_tableTag, "agendaItems") {
    def * = (_Id, proofid, initialproofnode, displayname) <> (AgendaitemsRow.tupled, AgendaitemsRow.unapply)
    
    /** Database column _id DBType(INTEGER), PrimaryKey */
    val _Id: Column[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)
    /** Database column proofId DBType(INTEGER) */
    val proofid: Column[Option[Int]] = column[Option[Int]]("proofId")
    /** Database column initialProofNode DBType(INTEGER) */
    val initialproofnode: Column[Option[Int]] = column[Option[Int]]("initialProofNode")
    /** Database column displayName DBType(STRING) */
    val displayname: Column[Option[String]] = column[Option[String]]("displayName")
    
    /** Foreign key referencing Proofs (database name proofs_FK_1) */
    lazy val proofsFk = foreignKey("proofs_FK_1", proofid, Proofs)(r => r._Id, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
  }
  /** Collection-like TableQuery object for table Agendaitems */
  lazy val Agendaitems = new TableQuery(tag => new Agendaitems(tag))
  
  /** Entity class storing rows of table Config
   *  @param configid Database column configId DBType(INTEGER), PrimaryKey
   *  @param configname Database column configName DBType(TEXT)
   *  @param key Database column key DBType(TEXT)
   *  @param value Database column value DBType(TEXT) */
  case class ConfigRow(configid: Option[Int], configname: Option[String], key: Option[String], value: Option[String])
  /** GetResult implicit for fetching ConfigRow objects using plain SQL queries */
  implicit def GetResultConfigRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[ConfigRow] = GR{
    prs => import prs._
    ConfigRow.tupled((<<?[Int], <<?[String], <<?[String], <<?[String]))
  }
  /** Table description of table config. Objects of this class serve as prototypes for rows in queries. */
  class Config(_tableTag: Tag) extends Table[ConfigRow](_tableTag, "config") {
    def * = (configid, configname, key, value) <> (ConfigRow.tupled, ConfigRow.unapply)
    
    /** Database column configId DBType(INTEGER), PrimaryKey */
    val configid: Column[Option[Int]] = column[Option[Int]]("configId", O.PrimaryKey)
    /** Database column configName DBType(TEXT) */
    val configname: Column[Option[String]] = column[Option[String]]("configName")
    /** Database column key DBType(TEXT) */
    val key: Column[Option[String]] = column[Option[String]]("key")
    /** Database column value DBType(TEXT) */
    val value: Column[Option[String]] = column[Option[String]]("value")
  }
  /** Collection-like TableQuery object for table Config */
  lazy val Config = new TableQuery(tag => new Config(tag))
  
  /** Entity class storing rows of table Executables
   *  @param _Id Database column _id DBType(INTEGER), PrimaryKey
   *  @param belleexpr Database column belleExpr DBType(TEXT) */
  case class ExecutablesRow(_Id: Option[Int], belleexpr: Option[String])
  /** GetResult implicit for fetching ExecutablesRow objects using plain SQL queries */
  implicit def GetResultExecutablesRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[ExecutablesRow] = GR{
    prs => import prs._
    ExecutablesRow.tupled((<<?[Int], <<?[String]))
  }
  /** Table description of table executables. Objects of this class serve as prototypes for rows in queries. */
  class Executables(_tableTag: Tag) extends Table[ExecutablesRow](_tableTag, "executables") {
    def * = (_Id, belleexpr) <> (ExecutablesRow.tupled, ExecutablesRow.unapply)
    
    /** Database column _id DBType(INTEGER), PrimaryKey */
    val _Id: Column[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)
    /** Database column belleExpr DBType(TEXT) */
    val belleexpr: Column[Option[String]] = column[Option[String]]("belleExpr")
  }
  /** Collection-like TableQuery object for table Executables */
  lazy val Executables = new TableQuery(tag => new Executables(tag))
  
  /** Entity class storing rows of table Executionsteps
   *  @param _Id Database column _id DBType(INTEGER), PrimaryKey
   *  @param executionid Database column executionId DBType(INTEGER)
   *  @param previousstep Database column previousStep DBType(INTEGER)
   *  @param parentstep Database column parentStep DBType(INTEGER)
   *  @param branchorder Database column branchOrder DBType(INT)
   *  @param branchlabel Database column branchLabel DBType(TEXT)
   *  @param alternativeorder Database column alternativeOrder DBType(INT)
   *  @param status Database column status DBType(TEXT)
   *  @param executableid Database column executableId DBType(INTEGER)
   *  @param inputprovableid Database column inputProvableId DBType(INTEGER)
   *  @param resultprovableid Database column resultProvableId DBType(INTEGER)
   *  @param localprovableid Database column localProvableId DBType(INTEGER)
   *  @param userexecuted Database column userExecuted DBType(BOOLEAN)
   *  @param childrenrecorded Database column childrenRecorded DBType(BOOLEAN)
   *  @param rulename Database column ruleName DBType(STRING) */
  case class ExecutionstepsRow(_Id: Option[Int], executionid: Option[Int], previousstep: Option[Int], parentstep: Option[Int], branchorder: Option[Int], branchlabel: Option[String], alternativeorder: Option[Int], status: Option[String], executableid: Option[Int], inputprovableid: Option[Int], resultprovableid: Option[Int], localprovableid: Option[Int], userexecuted: Option[String], childrenrecorded: Option[String], rulename: Option[String])
  /** GetResult implicit for fetching ExecutionstepsRow objects using plain SQL queries */
  implicit def GetResultExecutionstepsRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[ExecutionstepsRow] = GR{
    prs => import prs._
    ExecutionstepsRow.tupled((<<?[Int], <<?[Int], <<?[Int], <<?[Int], <<?[Int], <<?[String], <<?[Int], <<?[String], <<?[Int], <<?[Int], <<?[Int], <<?[Int], <<?[String], <<?[String], <<?[String]))
  }
  /** Table description of table executionSteps. Objects of this class serve as prototypes for rows in queries. */
  class Executionsteps(_tableTag: Tag) extends Table[ExecutionstepsRow](_tableTag, "executionSteps") {
    def * = (_Id, executionid, previousstep, parentstep, branchorder, branchlabel, alternativeorder, status, executableid, inputprovableid, resultprovableid, localprovableid, userexecuted, childrenrecorded, rulename) <> (ExecutionstepsRow.tupled, ExecutionstepsRow.unapply)
    
    /** Database column _id DBType(INTEGER), PrimaryKey */
    val _Id: Column[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)
    /** Database column executionId DBType(INTEGER) */
    val executionid: Column[Option[Int]] = column[Option[Int]]("executionId")
    /** Database column previousStep DBType(INTEGER) */
    val previousstep: Column[Option[Int]] = column[Option[Int]]("previousStep")
    /** Database column parentStep DBType(INTEGER) */
    val parentstep: Column[Option[Int]] = column[Option[Int]]("parentStep")
    /** Database column branchOrder DBType(INT) */
    val branchorder: Column[Option[Int]] = column[Option[Int]]("branchOrder")
    /** Database column branchLabel DBType(TEXT) */
    val branchlabel: Column[Option[String]] = column[Option[String]]("branchLabel")
    /** Database column alternativeOrder DBType(INT) */
    val alternativeorder: Column[Option[Int]] = column[Option[Int]]("alternativeOrder")
    /** Database column status DBType(TEXT) */
    val status: Column[Option[String]] = column[Option[String]]("status")
    /** Database column executableId DBType(INTEGER) */
    val executableid: Column[Option[Int]] = column[Option[Int]]("executableId")
    /** Database column inputProvableId DBType(INTEGER) */
    val inputprovableid: Column[Option[Int]] = column[Option[Int]]("inputProvableId")
    /** Database column resultProvableId DBType(INTEGER) */
    val resultprovableid: Column[Option[Int]] = column[Option[Int]]("resultProvableId")
    /** Database column localProvableId DBType(INTEGER) */
    val localprovableid: Column[Option[Int]] = column[Option[Int]]("localProvableId")
    /** Database column userExecuted DBType(BOOLEAN) */
    val userexecuted: Column[Option[String]] = column[Option[String]]("userExecuted")
    /** Database column childrenRecorded DBType(BOOLEAN) */
    val childrenrecorded: Column[Option[String]] = column[Option[String]]("childrenRecorded")
    /** Database column ruleName DBType(STRING) */
    val rulename: Column[Option[String]] = column[Option[String]]("ruleName")
    
    /** Foreign key referencing Executables (database name executables_FK_1) */
    lazy val executablesFk = foreignKey("executables_FK_1", executableid, Executables)(r => r._Id, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
    /** Foreign key referencing Executionsteps (database name executionSteps_FK_2) */
    lazy val executionstepsFk = foreignKey("executionSteps_FK_2", (parentstep, previousstep), Executionsteps)(r => (r._Id, r._Id), onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
    /** Foreign key referencing Tacticexecutions (database name tacticExecutions_FK_3) */
    lazy val tacticexecutionsFk = foreignKey("tacticExecutions_FK_3", executionid, Tacticexecutions)(r => r._Id, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
  }
  /** Collection-like TableQuery object for table Executionsteps */
  lazy val Executionsteps = new TableQuery(tag => new Executionsteps(tag))
  
  /** Entity class storing rows of table Lemmas
   *  @param _Id Database column _id DBType(INTEGER), PrimaryKey
   *  @param lemma Database column lemma DBType(TEXT) */
  case class LemmasRow(_Id: Option[Int], lemma: Option[String])
  /** GetResult implicit for fetching LemmasRow objects using plain SQL queries */
  implicit def GetResultLemmasRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[LemmasRow] = GR{
    prs => import prs._
    LemmasRow.tupled((<<?[Int], <<?[String]))
  }
  /** Table description of table lemmas. Objects of this class serve as prototypes for rows in queries. */
  class Lemmas(_tableTag: Tag) extends Table[LemmasRow](_tableTag, "lemmas") {
    def * = (_Id, lemma) <> (LemmasRow.tupled, LemmasRow.unapply)
    
    /** Database column _id DBType(INTEGER), PrimaryKey */
    val _Id: Column[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)
    /** Database column lemma DBType(TEXT) */
    val lemma: Column[Option[String]] = column[Option[String]]("lemma")
  }
  /** Collection-like TableQuery object for table Lemmas */
  lazy val Lemmas = new TableQuery(tag => new Lemmas(tag))
  
  /** Entity class storing rows of table Models
   *  @param _Id Database column _id DBType(INTEGER), PrimaryKey
   *  @param userid Database column userId DBType(TEXT)
   *  @param name Database column name DBType(TEXT)
   *  @param date Database column date DBType(TEXT)
   *  @param description Database column description DBType(TEXT)
   *  @param filecontents Database column fileContents DBType(TEXT)
   *  @param publink Database column publink DBType(TEXT)
   *  @param title Database column title DBType(TEXT)
   *  @param tactic Database column tactic DBType(TEXT) */
  case class ModelsRow(_Id: Option[Int], userid: Option[String], name: Option[String], date: Option[String], description: Option[String], filecontents: Option[String], publink: Option[String], title: Option[String], tactic: Option[String])
  /** GetResult implicit for fetching ModelsRow objects using plain SQL queries */
  implicit def GetResultModelsRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[ModelsRow] = GR{
    prs => import prs._
    ModelsRow.tupled((<<?[Int], <<?[String], <<?[String], <<?[String], <<?[String], <<?[String], <<?[String], <<?[String], <<?[String]))
  }
  /** Table description of table models. Objects of this class serve as prototypes for rows in queries. */
  class Models(_tableTag: Tag) extends Table[ModelsRow](_tableTag, "models") {
    def * = (_Id, userid, name, date, description, filecontents, publink, title, tactic) <> (ModelsRow.tupled, ModelsRow.unapply)
    
    /** Database column _id DBType(INTEGER), PrimaryKey */
    val _Id: Column[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)
    /** Database column userId DBType(TEXT) */
    val userid: Column[Option[String]] = column[Option[String]]("userId")
    /** Database column name DBType(TEXT) */
    val name: Column[Option[String]] = column[Option[String]]("name")
    /** Database column date DBType(TEXT) */
    val date: Column[Option[String]] = column[Option[String]]("date")
    /** Database column description DBType(TEXT) */
    val description: Column[Option[String]] = column[Option[String]]("description")
    /** Database column fileContents DBType(TEXT) */
    val filecontents: Column[Option[String]] = column[Option[String]]("fileContents")
    /** Database column publink DBType(TEXT) */
    val publink: Column[Option[String]] = column[Option[String]]("publink")
    /** Database column title DBType(TEXT) */
    val title: Column[Option[String]] = column[Option[String]]("title")
    /** Database column tactic DBType(TEXT) */
    val tactic: Column[Option[String]] = column[Option[String]]("tactic")
    
    /** Foreign key referencing Users (database name users_FK_1) */
    lazy val usersFk = foreignKey("users_FK_1", userid, Users)(r => r.email, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
  }
  /** Collection-like TableQuery object for table Models */
  lazy val Models = new TableQuery(tag => new Models(tag))
  
  /** Entity class storing rows of table Proofs
   *  @param _Id Database column _id DBType(INTEGER), PrimaryKey
   *  @param modelid Database column modelId DBType(INTEGER)
   *  @param name Database column name DBType(TEXT)
   *  @param description Database column description DBType(TEXT)
   *  @param date Database column date DBType(TEXT)
   *  @param closed Database column closed DBType(INTEGER) */
  case class ProofsRow(_Id: Option[Int], modelid: Option[Int], name: Option[String], description: Option[String], date: Option[String], closed: Option[Int])
  /** GetResult implicit for fetching ProofsRow objects using plain SQL queries */
  implicit def GetResultProofsRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[ProofsRow] = GR{
    prs => import prs._
    ProofsRow.tupled((<<?[Int], <<?[Int], <<?[String], <<?[String], <<?[String], <<?[Int]))
  }
  /** Table description of table proofs. Objects of this class serve as prototypes for rows in queries. */
  class Proofs(_tableTag: Tag) extends Table[ProofsRow](_tableTag, "proofs") {
    def * = (_Id, modelid, name, description, date, closed) <> (ProofsRow.tupled, ProofsRow.unapply)
    
    /** Database column _id DBType(INTEGER), PrimaryKey */
    val _Id: Column[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)
    /** Database column modelId DBType(INTEGER) */
    val modelid: Column[Option[Int]] = column[Option[Int]]("modelId")
    /** Database column name DBType(TEXT) */
    val name: Column[Option[String]] = column[Option[String]]("name")
    /** Database column description DBType(TEXT) */
    val description: Column[Option[String]] = column[Option[String]]("description")
    /** Database column date DBType(TEXT) */
    val date: Column[Option[String]] = column[Option[String]]("date")
    /** Database column closed DBType(INTEGER) */
    val closed: Column[Option[Int]] = column[Option[Int]]("closed")
    
    /** Foreign key referencing Models (database name models_FK_1) */
    lazy val modelsFk = foreignKey("models_FK_1", modelid, Models)(r => r._Id, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
  }
  /** Collection-like TableQuery object for table Proofs */
  lazy val Proofs = new TableQuery(tag => new Proofs(tag))
  
  /** Entity class storing rows of table Tacticexecutions
   *  @param _Id Database column _id DBType(INTEGER), PrimaryKey
   *  @param proofid Database column proofId DBType(INTEGER) */
  case class TacticexecutionsRow(_Id: Option[Int], proofid: Option[Int])
  /** GetResult implicit for fetching TacticexecutionsRow objects using plain SQL queries */
  implicit def GetResultTacticexecutionsRow(implicit e0: GR[Option[Int]]): GR[TacticexecutionsRow] = GR{
    prs => import prs._
    TacticexecutionsRow.tupled((<<?[Int], <<?[Int]))
  }
  /** Table description of table tacticExecutions. Objects of this class serve as prototypes for rows in queries. */
  class Tacticexecutions(_tableTag: Tag) extends Table[TacticexecutionsRow](_tableTag, "tacticExecutions") {
    def * = (_Id, proofid) <> (TacticexecutionsRow.tupled, TacticexecutionsRow.unapply)
    
    /** Database column _id DBType(INTEGER), PrimaryKey */
    val _Id: Column[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)
    /** Database column proofId DBType(INTEGER) */
    val proofid: Column[Option[Int]] = column[Option[Int]]("proofId")
    
    /** Foreign key referencing Proofs (database name proofs_FK_1) */
    lazy val proofsFk = foreignKey("proofs_FK_1", proofid, Proofs)(r => r._Id, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
  }
  /** Collection-like TableQuery object for table Tacticexecutions */
  lazy val Tacticexecutions = new TableQuery(tag => new Tacticexecutions(tag))
  
  /** Entity class storing rows of table Users
   *  @param email Database column email DBType(TEXT), PrimaryKey
   *  @param hash Database column hash DBType(TEXT)
   *  @param salt Database column salt DBType(TEXT)
   *  @param iterations Database column iterations DBType(INTEGER) */
  case class UsersRow(email: Option[String], hash: Option[String], salt: Option[String], iterations: Option[Int])
  /** GetResult implicit for fetching UsersRow objects using plain SQL queries */
  implicit def GetResultUsersRow(implicit e0: GR[Option[String]], e1: GR[Option[Int]]): GR[UsersRow] = GR{
    prs => import prs._
    UsersRow.tupled((<<?[String], <<?[String], <<?[String], <<?[Int]))
  }
  /** Table description of table users. Objects of this class serve as prototypes for rows in queries. */
  class Users(_tableTag: Tag) extends Table[UsersRow](_tableTag, "users") {
    def * = (email, hash, salt, iterations) <> (UsersRow.tupled, UsersRow.unapply)
    
    /** Database column email DBType(TEXT), PrimaryKey */
    val email: Column[Option[String]] = column[Option[String]]("email", O.PrimaryKey)
    /** Database column hash DBType(TEXT) */
    val hash: Column[Option[String]] = column[Option[String]]("hash")
    /** Database column salt DBType(TEXT) */
    val salt: Column[Option[String]] = column[Option[String]]("salt")
    /** Database column iterations DBType(INTEGER) */
    val iterations: Column[Option[Int]] = column[Option[Int]]("iterations")
  }
  /** Collection-like TableQuery object for table Users */
  lazy val Users = new TableQuery(tag => new Users(tag))
}