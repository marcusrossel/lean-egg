use egg::StopReason;

#[derive(Debug)]
pub enum Error {
    Init(String),
    Goal(String),
    Guide(String),
    Fact(String),
    Rewrite(String),
    Stopped(StopReason),
}

impl ToString for Error {

    fn to_string(&self) -> String {
        match self {
            Error::Init(s)                                => format!("⚡️ {s}"),
            Error::Goal(s)                                => format!("⚡️ {s}"),
            Error::Guide(s)                               => format!("⚡️ {s}"),
            Error::Fact(s)                                => format!("⚡️ {s}"),
            Error::Rewrite(s)                             => format!("⚡️ {s}"),
            Error::Stopped(StopReason::Saturated)         => "☹ saturated".to_string(),
            Error::Stopped(StopReason::TimeLimit(_))      => "☹ reached time limit".to_string(),
            Error::Stopped(StopReason::IterationLimit(_)) => "☹ reached iteration limit".to_string(),
            Error::Stopped(StopReason::NodeLimit(_))      => "☹ reached node limit".to_string(),
            Error::Stopped(StopReason::Other(s))          => format!("☹ {s}"),
        }
    }
}

pub type Res<T> = Result<T, Error>;